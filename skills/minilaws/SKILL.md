---
name: minilaws
description: Write and repair laws and proofs for minilaws, a proof checker for AI-edited code. Use it when a project has a minilaws.toml or *.laws files, when a minilaws hook reports "REJECTED", or when the user asks to state or prove a law (invariant) about their code.
---

# minilaws

The project's **laws** (`LAWS.laws`) are statements its code must always satisfy. They are
**human-owned**: a hook blocks you from editing them and `minilaws.toml`. After every edit to a file listed in
`minilaws.toml`, a hook re-checks every proof. If it reports `REJECTED`, your change broke a
law, or a proof no longer fits the code.

## When the hook rejects an edit

1. Read the message. It names the failing proof and shows `expected` versus `got`.
2. Decide whether the **code** is wrong (you introduced a bug) or the **proof** is stale (the
   code is right, but it now computes differently).
3. Fix the code or the proof. **Never** weaken a law, and never route around the check (for
   example, by deleting the `from minilaws import Nat` marker, moving code into a `.laws` file,
   or editing the laws or `minilaws.toml` through Bash).
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
inductive List (A : Type 0) : Type 0 where
  | nil : List A
  | cons : A -> List A -> List A  -- also generates List.rec
(x : A) -> B    A -> B            -- for all x : A, B   /   implication
{x : A} -> B    fun {x} => t      -- implicit argument (inferred)
@f A x                            -- pass implicits explicitly when inference fails
```

Built-ins: `Nat` (`zero`, `succ`, `Nat.rec`), `Eq a b` (`refl`, `Eq.rec`, `Eq.subst`).

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
- **Using another law** → apply it as a function, for example `symm (succ_add k a)`.
- Write a lambda's binder type when inference can't see it, for example
  `fun (l : List Nat) => ...`.

## Python subset (`.py` files in `minilaws.toml`)

These functions are checked, and they also run as normal Python:

```python
from minilaws import Nat

def add(n: Nat, m: Nat) -> Nat:
    if m == 0:
        return n
    return add(n, m - 1) + 1
```

Allowed:
- Parameters and results annotated `Nat`.
- At most one `if m == 0: return ...`, followed by one `return ...`.
- Recursion only as `f(..., m - 1, ...)`, with the other arguments unchanged.
- Literals, `x + <int>`, and calls to functions defined earlier in the same file.
- Imports only from `minilaws`.

A file with laws may only use the prelude, Python code and its own declarations. Put
helper lemmas in your proofs file, but never a `def` or `inductive` that a law relies on.

Anything else is rejected as `unsupported Python`. Rewrite the code into this shape. Don't
move it out of the checked files.
