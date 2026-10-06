# minilaws

A dependent-type proof checker in one pure-Python file (stdlib only), inspired by Bend's [`LAWS.bend`](https://github.com/HigherOrderCO/Bend).
**Types are statements, programs are proofs, and type checking is proof checking** (Curry-Howard).

You write ordinary Python, an AI is free to edit it, and the laws in `LAWS.laws` must keep holding. If an edit breaks a law, your tests fail.

## Usage

```
pip install git+https://github.com/luajapiassu/minilaws   # not on PyPI yet (https://github.com/luajapiassu/minilaws/issues/1)
```

1. Ask your AI to write your app's rules in `LAWS.laws` and to prove them.
2. Run `pytest` as usual. Every project with a `.laws` file that pytest collects becomes one test, so a CI that already runs your tests now enforces the laws too.
3. Protect the laws in review (see [Who owns the laws](#who-owns-the-laws)).

If your pytest config narrows collection (`testpaths`, `--ignore`), make sure it still reaches the `.laws` files, or run `minilaws check` in CI.

You can also check without pytest:

```
minilaws check            # current directory
minilaws check path/to/project
minilaws check --against origin/main   # also: the laws are still the ones on main
```

No configuration is needed. minilaws checks:
- every `*.laws` file;
- every `.py` file that does `from minilaws import Nat`.

File order doesn't matter: code is checked first, then laws, then proofs, and within each step a declaration comes after the ones it uses. To pick the files explicitly, add a `minilaws.toml` with `files = [...]`.

A folder with its own `LAWS.laws` or `minilaws.toml` is a separate project: the parent's check skips it, and it gets its own test.

Delete the `+ 1` in `examples/app.py`. The code still runs, but it's now wrong:

```
REJECTED: proofs.laws: proof zero_add: type mismatch in 'cong succ ih'
```

## Who owns the laws

The laws are only worth something if the AI can't change what they say. minilaws closes the routes it can see:

- A file that contains `law`s is human-owned. Its laws, `def`s and `inductive`s may use only the prelude, Python code (`.py`) and its own declarations. A law can't depend on something defined in `proofs.laws`, where the AI could change its meaning. This includes `theorem`s in that file, so put helper lemmas in your proofs file ([#7](https://github.com/luajapiassu/minilaws/issues/7)).
- Python files may only import from `minilaws`, and may only call functions defined earlier in the same file, so the code that's checked is the code that runs.
- Deleting or renaming `LAWS.laws` leaves its proofs without laws, which fails the check.

The other route is changing the laws themselves: weakening one, or deleting a law together with its proof. Inside one version of the code that's invisible, since the weaker laws really are proved. So minilaws does what Lean's [`comparator`](https://github.com/leanprover/comparator) does with a challenge file: it takes the laws from a version the change can't touch and compares.

```
minilaws check --against origin/main
```

Every law at `origin/main` must still exist, with the same statement and the same dependencies, taken transitively. A `def` or `inductive` in a laws file must be identical. Code is compared by signature and by the file it comes from, because the code is what's allowed to change. Renaming a binder or editing comments isn't a change, and new laws are fine. Anything else is rejected:

```
REJECTED: the laws differ from origin/main; a human must approve this:
  law add_assoc: removed
```

In CI, run it against the PR's base branch. The pytest plugin doesn't take `--against` yet ([#8](https://github.com/luajapiassu/minilaws/issues/8)), so it's a separate step:

```yaml
- uses: actions/checkout@v4
  with: { fetch-depth: 0 }
- run: pip install git+https://github.com/luajapiassu/minilaws
- run: minilaws check --against origin/${{ github.base_ref }}
```

When a law change is intentional, this step fails by design, and a human has to approve the change. Protect `LAWS.laws` and `minilaws.toml` with `CODEOWNERS` plus branch protection, so that approval comes from someone the AI isn't. Other ways to approve are in [#5](https://github.com/luajapiassu/minilaws/issues/5). For example:

```
LAWS.laws        @you
minilaws.toml    @you
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
- Literals, `x + <int>`, and calls to functions defined earlier in the same file.
- Imports only from `minilaws`.

Anything else is refused with `unsupported Python (...)`, so a checked module holds only these functions: keep other code in modules that import them. Checked modules can't call each other yet ([#6](https://github.com/luajapiassu/minilaws/issues/6)). `Nat = int`, and the laws speak about `n >= 0`.

## Optional: Claude Code plugin

This gives faster feedback during a session: Claude sees a broken law right after the edit, not only when the tests run.

```
/plugin marketplace add luajapiassu/minilaws
/plugin install minilaws@minilaws
```

Unlike pytest, the plugin needs a `minilaws.toml` with `files` and `laws`. It blocks edits to the laws files and to `minilaws.toml`, re-checks after every edit, and ships a skill with the usual proof patterns. If the hook itself fails (bad config, missing file), it rejects the edit rather than letting it through.

Edits made through Bash aren't watched during the session ([#3](https://github.com/luajapiassu/minilaws/issues/3)). The real enforcement is pytest/CI: `minilaws check --against` catches a changed law however it was edited.

## Why the guarantee holds

- Predicative universes (`Type 0 : Type 1`), and constructor fields must fit in `Type 0`, so there's no `Type : Type` paradox.
- Inductive types must be strictly positive, and a definition can't call itself. Every term terminates, so there are no looping "proofs".
- An unproved `law` isn't in scope, so it can't be used as a hypothesis.
- For proofs, the elaborator (implicit arguments) is **not trusted**. The kernel (`whnf`, `conv`, `infer`, `check`, recursor generation) re-checks its fully explicit output.
- For law statements, the elaborator **is** trusted: the kernel checks that a statement is well-formed, not that it says what you wrote.
- The Python translator **is** trusted, so keep its subset small.

## Limitations

- Recursors only eliminate into `Type 0`, so there is no large elimination: you can't prove that constructors differ (`zero ≠ succ n`) or other negative statements.
- Unary `Nat`: a huge literal like `n + 5000` is rejected as too deep to check.

Details and possible ways out: [#9](https://github.com/luajapiassu/minilaws/issues/9).

## Development

```
python -m venv .venv && .venv/Scripts/pip install -e . pytest   # Windows; use .venv/bin on Unix
.venv/Scripts/python -m pytest
```

## References

- [Bend](https://github.com/HigherOrderCO/Bend): the `LAWS.bend` idea (laws a human writes, proofs the AI must keep valid) that minilaws ports to Python.
- [Lean's `comparator`](https://github.com/leanprover/comparator): checks a solution against a challenge file the author controls (identical statements, including dependencies, plus permitted axioms). It's the model for `check --against`.
- [Claude's Fermat's Last Theorem Lean proof](https://explainx.ai/blog/anthropic-claude-fermats-last-theorem-lean-proof-2026): comparator in practice, with human review of the statement on top of the kernel check.
- [Formal proof cost collapse (Navier-Stokes in Lean 4)](https://explainx.ai/blog/lean-4-formal-proof-cost-collapse-navier-stokes-2026): states the gap minilaws has to close: a kernel proves the proof follows from the statement, not that the statement is the right one.
- [Bend 2 overview](https://akitaonrails.com/en/2026/09/19/new-ai-language-just-released-bend-2/): the `LAWS.bend` / `PROOF.bend` workflow, which assumes the laws file stays human-written.

## License

MIT
