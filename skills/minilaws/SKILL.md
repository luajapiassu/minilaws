---
name: minilaws
description: Write and repair laws and proofs for minilaws, a proof checker for AI-edited code. Use it when a project has a minilaws.toml or *.laws files, when a minilaws hook reports "REJECTED", or when the user asks to state or prove a law (invariant) about their code.
---

# minilaws

The project's **laws** (`LAWS.laws`) are statements its code must always satisfy. They are
**human-owned**: a hook blocks you from editing any file with a `law` and `minilaws.toml`, and
reports it if a Bash command changes them. After every edit to a checked file, a hook re-checks
every proof. If it reports `REJECTED`, your change broke a
law, or a proof no longer fits the code.

## When the hook rejects an edit

1. Read the message. It names the failing proof and shows `expected` versus `got`.
2. Decide whether the **code** is wrong (you introduced a bug) or the **proof** is stale (the
   code is right, but it now computes differently).
3. Fix the code or the proof. **Never** weaken a law, and never route around the check (for
   example, by deleting the `from minilaws import Nat` marker, moving code into a `.laws` file,
   or editing the laws or `minilaws.toml` through Bash: the hook sees that too).
4. If you believe a law itself is wrong, stop and ask the user.

If a check says `the laws differ from <ref>`, a law was changed, removed, or now depends on
different code than in the trusted version. Undo that. Only the user can change the laws.

Run the check by hand with `minilaws check` (or `python <plugin>/minilaws.py check`).

## Language

```
def name : T := t                 -- code
law name : T                      -- statement only (LAWS.laws)
proof name := t                   -- proof of a law declared earlier
theorem name : T := t             -- helper lemma: statement + proof
inductive Tree (A : Type 0) : Type 0 where
  | leaf : Tree A
  | node : Tree A -> A -> Tree A -> Tree A  -- also generates Tree.rec
(x : A) -> B    A -> B            -- for all x : A, B   /   implication
{x : A} -> B    fun {x} => t      -- implicit argument (inferred)
@f A x                            -- pass implicits explicitly when inference fails
```

Built-ins: `Nat` (`zero`, `succ`, `Nat.rec`), `Eq a b` (`refl`, `Eq.rec`, `Eq.subst`),
`Empty`, `Unit` (`tt`), `Not A` (= `A -> Empty`), `Bool` (`false`, `true`; `Bool.rec` takes
the `false` case first), `List A` (`nil`, `cons`, `List.rec`), `Bool.cond c t e`, `Bool.not`,
`Bool.and`, `Bool.or`, `Nat.eqb`, `Nat.ltb`. Every inductive `T` also gets `T.rec1`.

## Proof patterns

- **True by computation** → `refl`. Example: `add n zero` reduces to `n`.
- **Induction** → `T.rec motive case1 case2 ... x`. The motive is the statement as a
  function of the induction variable:
  ```
  proof zero_add := fun n =>
    Nat.rec (fun k => Eq (add zero k) k) refl (fun k ih => cong succ ih) n
  ```
  Each case takes the constructor's fields, then one `ih` per recursive field.
- **Rewriting** → derive lemmas from `Eq.subst P h px`. If the project doesn't already have
  `cong`, `symm` and `trans`, add them as theorems:
  ```
  theorem cong : {A B : Type 0} -> {a b : A} -> (f : A -> B) -> Eq a b -> Eq (f a) (f b) :=
    fun {A B a b} f h => Eq.subst (fun x => Eq (f a) (f x)) h refl
  theorem symm : {A : Type 0} -> {a b : A} -> Eq a b -> Eq b a :=
    fun {A a b} h => Eq.subst (fun x => Eq x a) h refl
  theorem trans : {A : Type 0} -> {a b c : A} -> Eq a b -> Eq b c -> Eq a c :=
    fun {A a b c} h1 h2 => Eq.subst (fun x => Eq a x) h2 h1
  ```
- **Constructors differ / "never happens"** → `Not (...)`. Define a type by recursion
  with `T.rec1` (motive in `Type 1`), `Unit` on one constructor and `Empty` on the others,
  then transport `tt` along the impossible equation:
  ```
  def IsZero : Nat -> Type 0 := fun n => Nat.rec1 (fun _ => Type 0) Unit (fun _ _ => Empty) n
  theorem zero_ne_succ : (n : Nat) -> Not (Eq zero (succ n)) := fun n h => Eq.subst IsZero h tt
  ```
- **Using another law** → apply it as a function, for example `symm (succ_add k a)`.
- Write a lambda's binder type when inference can't see it, for example
  `fun (l : List Nat) => ...`.

## Python subset (`.py` files with `from minilaws import Nat`)

These functions are checked, and they also run as normal Python:

```python
from minilaws import Nat

def add(n: Nat, m: Nat) -> Nat:
    if m == 0:
        return n
    return add(n, m - 1) + 1

def cat(xs: list[Nat], ys: list[Nat]) -> list[Nat]:
    if not xs:
        return ys
    return [xs[0]] + cat(xs[1:], ys)
```

Allowed:
- Parameters and results annotated `Nat`, `bool` or `list[...]` of those.
- At most one `if ...: return ...`, followed by one `return ...`. With `if m == 0` (Nat
  parameter) or `if not xs` (list parameter) it's structural recursion: `f(..., m - 1, ...)`
  or `f(..., xs[1:], ...)`; `xs[0]` and `xs[1:]` only there. The other arguments may change
  (accumulators): then the translation's motive takes them, `Nat.rec (fun _ => A -> R) ... m a`,
  and a proof about it inducts with the accumulator generalized:
  `Nat.rec (fun m => (a : A) -> P a m) (fun a => ...) (fun m ih a => ... ih (...) ...) m a`.
  Any other condition is a plain if-then-else, without recursion.
- Literals, `True`/`False`, `x + <int>`, comparisons of `Nat`s (not chained), `and`/`or`/`not`,
  `a if c else b`, list literals, `[a, ...] + xs`, and calls to functions defined earlier in
  the same file.
- Imports only from `minilaws`.

In the laws, `if c` is `Bool.cond c ...`, `a < b` is `Nat.ltb a b`, `a == b` is `Nat.eqb a b`,
and `[x] + xs` is `cons x xs`. Prove things about them with `Bool.rec`/`Nat.rec`/`List.rec`.

A file with laws may only use the prelude, Python code and its own declarations. Put
helper lemmas in your proofs file, but never a `def` or `inductive` that a law relies on.

Anything else is rejected as `unsupported Python`. Rewrite the code into this shape. Don't
move it out of the checked files.
