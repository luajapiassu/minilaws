# minilaws

A dependent-type proof checker in one pure-Python file (stdlib only), inspired by Bend's `LAWS.bend`.
**Types are statements, programs are proofs, and type checking is proof checking** (Curry-Howard).

You write ordinary Python, an AI is free to edit it, and a human owns `LAWS.laws`. If an edit breaks a law, the build fails.

```
python minilaws.py examples/app.py examples/LAWS.laws examples/proofs.laws
OK: 9 declarations checked
```

Delete the `+ 1` in `app.py`. The code still runs, but it's now wrong:

```
REJECTED: proof zero_add: type mismatch in 'cong succ ih'
```

## Claude Code plugin

```
/plugin marketplace add <path or github user/repo>
/plugin install minilaws@minilaws
```

Add a `minilaws.toml` to your project:

```toml
files = ["app.py", "LAWS.laws", "proofs.laws"]   # checked in this order
laws = ["LAWS.laws"]                              # human-owned
```

- **PreToolUse hook:** Claude can't edit the laws files.
- **PostToolUse hook:** after each edit to a listed file, every proof is re-checked. A failure goes back to Claude, which has to fix the code or the proof.
- **`minilaws` skill:** teaches Claude the syntax and the usual proof patterns.

## Syntax

```
def name : T := t                 -- code
law name : T                      -- obligation (human-owned)
proof name := t                   -- discharges a law
theorem name : T := t             -- law + proof in one step
inductive List (A : Type 0) : Type 0 where
  | nil : List A
  | cons : A -> List A -> List A  -- generates List.rec (= induction on lists)
{x : A} -> B   fun {x} => t       -- implicit arguments, inferred by unification
@f A x                            -- pass implicit arguments explicitly
```

The prelude defines `Nat` and `Eq` with `inductive` itself, so the kernel has no special cases.

## Python subset (`.py` files)

```python
def add(n: Nat, m: Nat) -> Nat:
    if m == 0:
        return n
    return add(n, m - 1) + 1
```

Supported:
- Functions over `Nat`.
- Structural recursion `f(..., m - 1, ...)` after `if m == 0`, with the other arguments unchanged.
- Literals, `x + <int>`, and calls to earlier functions.

Anything else is refused with `unsupported Python (...)`. `Nat = int`, and the laws speak about `n >= 0`.

## Why the guarantee holds

- Predicative universes (`Type 0 : Type 1`), and constructor fields must fit in `Type 0`, so there's no `Type : Type` paradox.
- Inductive types must be strictly positive, and a definition can't call itself. Every term terminates, so there are no looping "proofs".
- An unproved `law` isn't in scope, so it can't be used as a hypothesis.
- The elaborator (implicit arguments) is **not trusted**. The kernel (`whnf`, `conv`, `infer`, `check`, recursor generation) re-checks its fully explicit output.
- The Python translator **is** trusted, so keep its subset small.

Tests: `python test_minilaws.py` (or `pytest`).
