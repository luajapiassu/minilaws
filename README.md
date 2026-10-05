# minilaws

A dependent-type proof checker in one pure-Python file (stdlib only), inspired by Bend's `LAWS.bend`.
**Types are statements, programs are proofs, and type checking is proof checking** (Curry-Howard).

You write ordinary Python, an AI is free to edit it, and the laws in `LAWS.laws` must keep holding. If an edit breaks a law, your tests fail.

## Usage

```
pip install minilaws
```

1. Ask your AI to write your app's rules in `LAWS.laws` and to prove them.
2. Run `pytest` as usual. Every `LAWS.laws` that pytest collects becomes a test, so a CI that already runs your tests now enforces the laws too.

You can also check without pytest:

```
minilaws check            # current directory
minilaws check path/to/project
```

No configuration is needed. minilaws checks:
- every `*.laws` file;
- every `.py` file that does `from minilaws import Nat`.

File order doesn't matter: code is checked first, then laws, then proofs. To pick the files explicitly, add a `minilaws.toml` with `files = [...]`.

Delete the `+ 1` in `examples/app.py`. The code still runs, but it's now wrong:

```
REJECTED: proofs.laws: proof zero_add: type mismatch in 'cong succ ih'
```

## Syntax

```
def name : T := t                 -- code
law name : T                      -- statement (LAWS.laws)
proof name := t                   -- proof of a law
theorem name : T := t             -- helper lemma: statement + proof
inductive List (A : Type 0) : Type 0 where
  | nil : List A
  | cons : A -> List A -> List A  -- generates List.rec (= induction on lists)
{x : A} -> B   fun {x} => t       -- implicit arguments, inferred by unification
@f A x                            -- pass implicit arguments explicitly
```

The prelude defines `Nat` and `Eq` with `inductive` itself, so the kernel has no special cases.

## Python subset

```python
from minilaws import Nat

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

## Optional: Claude Code plugin

This gives faster feedback during a session: Claude sees a broken law right after the edit, not only when the tests run.

```
/plugin marketplace add luajapiassu/minilaws
/plugin install minilaws@minilaws
```

It needs a `minilaws.toml` with `files` and `laws`. It blocks edits to the laws files, re-checks after every edit, and ships a skill with the usual proof patterns.

Edits made through Bash aren't watched (see issue #3). The real enforcement is pytest/CI.

## Why the guarantee holds

- Predicative universes (`Type 0 : Type 1`), and constructor fields must fit in `Type 0`, so there's no `Type : Type` paradox.
- Inductive types must be strictly positive, and a definition can't call itself. Every term terminates, so there are no looping "proofs".
- An unproved `law` isn't in scope, so it can't be used as a hypothesis.
- The elaborator (implicit arguments) is **not trusted**. The kernel (`whnf`, `conv`, `infer`, `check`, recursor generation) re-checks its fully explicit output.
- The Python translator **is** trusted, so keep its subset small.

## Development

```
python -m venv .venv && .venv/Scripts/pip install -e . pytest   # Windows; use .venv/bin on Unix
.venv/Scripts/python -m pytest
```

## License

MIT
