import shutil
import subprocess
import sys
import tempfile
import textwrap
from pathlib import Path

from minilaws import CheckError, Const, Env, check_project, check_source, main, read_source, translate_python

ROOT = Path(__file__).parent
EX = ROOT / "examples"
APP, LAWS, PROOFS = (read_source(EX / f) for f in ("app.py", "LAWS.laws", "proofs.laws"))

ADD = "def add : Nat -> Nat -> Nat := fun n m => Nat.rec (fun _ => Nat) n (fun _ ih => succ ih) m\n"


def rejects(src, needle=""):
    try:
        check_source(src)
    except CheckError as e:
        assert needle in str(e), str(e)
        return
    raise AssertionError(f"accepted but should reject:\n{src}")


def test_examples_check():
    env = Env()
    for src in (APP, LAWS, PROOFS):
        check_source(src, env)
    assert not env.laws


def test_false_law_cannot_be_proved():
    rejects(ADD + "law bad : (n : Nat) -> Eq (add n zero) zero\nproof bad := fun n => refl", "type mismatch")


def test_unproved_law_is_not_usable():
    rejects("law l : Eq zero zero\ntheorem t : Eq zero zero := l", "unknown name 'l'")


def test_no_self_recursion():
    # a looping "proof" of anything would make the logic inconsistent
    rejects("def loop : (A : Type 0) -> A := fun A => loop A", "unknown name 'loop'")


def test_no_type_in_type():
    rejects("def t : Type 0 := Type 0", "type mismatch")


def test_no_redefining():
    rejects("def zero : Nat := succ zero", "already declared")


# ---------- implicit arguments ----------

def test_implicit_args_inferred_from_expected_type():
    check_source(ADD + "theorem t : (n : Nat) -> Eq (add n zero) n := fun n => refl")


def test_implicit_args_inferred_from_other_args():
    check_source("""
theorem symm : {a b : Nat} -> Eq a b -> Eq b a :=
  fun {a b} h => Eq.subst (fun x => Eq x a) h refl
theorem t : (n : Nat) -> Eq n n -> Eq n n := fun n h => symm h
""")


def test_implicit_lambda_inserted_automatically():
    check_source("theorem t : {A : Type 0} -> {x : A} -> Eq x x := refl")


def test_at_passes_implicits_explicitly():
    check_source("theorem t : Eq zero zero := @refl Nat zero")


def test_uninferable_implicit_is_reported():
    rejects("theorem t : Eq zero zero := Eq.subst (fun x => Eq zero zero) refl refl", "could not infer")


def test_kernel_rechecks_elaborator_output():
    # the elaborator is not trusted: a bogus elaboration must still be rejected
    env = Env()
    real = env.elab_check
    env.elab_check = lambda ctx, t, ty: Const("zero") if t == Const("refl") else real(ctx, t, ty)
    try:
        check_source("theorem t : Eq zero zero := refl", env)
    except CheckError as e:
        assert "type mismatch" in str(e)
        return
    raise AssertionError("kernel accepted a bogus elaboration")


# ---------- user-defined inductive types ----------

LIST = ADD + (EX / "proofs.laws").read_text(encoding="utf-8").split("-- By computation")[0] + """
inductive List (A : Type 0) : Type 0 where
  | nil : List A
  | cons : A -> List A -> List A
def length : {A : Type 0} -> List A -> Nat :=
  fun xs => List.rec (fun _ => Nat) zero (fun _ _ ih => succ ih) xs
def append : {A : Type 0} -> List A -> List A -> List A :=
  fun {A} xs ys => List.rec (fun _ => List A) ys (fun x _ ih => cons x ih) xs
"""


def test_user_inductive_computes():
    check_source(LIST + "theorem t : Eq (length (cons zero (cons zero nil))) (succ (succ zero)) := refl")


def test_law_about_user_inductive_by_induction():
    check_source(LIST + """
law length_append : {A : Type 0} -> (xs ys : List A) -> Eq (length (append xs ys)) (add (length ys) (length xs))
proof length_append := fun {A} xs ys =>
  List.rec (fun l => Eq (length (append l ys)) (add (length ys) (length l))) refl (fun x l ih => cong succ ih) xs
""")


def test_nat_and_eq_are_ordinary_inductives():
    env = Env()
    assert {"Nat.rec", "Eq.rec"} <= env.types.keys()
    check_source("theorem t : {A : Type 0} -> {a b : A} -> Eq a b -> Eq b a := fun {A a b} h => Eq.rec (fun y _ => Eq y a) refl h")


def test_rejects_non_positive_inductive():
    # would allow a non-terminating "proof" of anything
    rejects("inductive Bad : Type 0 where\n  | mk : (Bad -> Nat) -> Bad", "positiv")


def test_rejects_too_large_field():
    # a Type 0 value holding a Type 0 is Type : Type in disguise
    rejects("inductive Box : Type 0 where\n  | mk : Type 0 -> Box", "universe")


def test_rejects_constructor_of_another_type():
    rejects("inductive T : Type 0 where\n  | mk : Nat", "must return T")
    rejects("inductive L (A : Type 0) : Type 0 where\n  | mk : L Nat", "must return L A")


# ---------- Python -> minilaws ----------

PY_ADD = """
from minilaws import Nat

def add(n: Nat, m: Nat) -> Nat:
    if m == 0:
        return n
    return add(n, m - 1) + 1
"""


def test_python_function_runs_and_is_checked():
    ns = {}
    exec(PY_ADD, ns)
    assert ns["add"](2, 3) == 5
    check_source(translate_python(PY_ADD) + LAWS + PROOFS)


def test_python_ai_edit_breaks_laws():
    # "AI refactor": drops the + 1. Still runs, now wrong; the laws catch it.
    rejects(translate_python(PY_ADD.replace("m - 1) + 1", "m - 1)")) + LAWS + PROOFS, "type mismatch")


def py(src):
    return textwrap.dedent(src).lstrip()


def test_python_base_case_sees_zero():
    # in the base case m is 0, not the original argument
    src = py("""
        def f(m: Nat) -> Nat:
            if m == 0:
                return m + 1
            return f(m - 1)
        """)
    ns = {"Nat": int}
    exec(src, ns)
    assert ns["f"](2) == 1
    check_source(translate_python(src) + "theorem t : Eq (f (succ (succ zero))) (succ zero) := refl")


def test_python_calls_other_functions():
    src = PY_ADD + py("""
        def double(n: Nat) -> Nat:
            return add(n, n)
        """)
    check_source(translate_python(src) + "theorem t : Eq (double (succ zero)) (succ (succ zero)) := refl")


UNSUPPORTED = [
    """
    def f(n: Nat) -> Nat:
        while n:
            n = n - 1
        return n
    """,
    """
    def f(n: Nat) -> Nat:  # not structural
        if n == 0:
            return 0
        return f(n - 2)
    """,
    """
    def f(n: Nat, m: Nat) -> Nat:  # the other argument changes in the recursive call
        if m == 0:
            return n
        return f(n + 1, m - 1)
    """,
    """
    def f(n: int) -> int:  # not Nat
        return n
    """,
    """
    def f(n: Nat) -> Nat:  # n - 1 is only a Nat when n > 0
        return n - 1
    """,
    """
    def f(n: Nat) -> Nat:  # recursion without a base case
        return f(n)
    """,
    """
    def f(n: Nat, m: Nat) -> Nat:  # + only with a constant; call add() otherwise
        return n + m
    """,
]


def test_python_unsupported_is_rejected():
    for bad in UNSUPPORTED:
        try:
            translate_python(py(bad))
        except CheckError as e:
            assert "unsupported" in str(e), str(e)
            continue
        raise AssertionError(f"translated unsupported code:{bad}")


def test_cli_checks_python_against_laws():
    assert main([str(EX / f) for f in ("app.py", "LAWS.laws", "proofs.laws")]) == 0


# ---------- zero-config project check ----------

def make_project(names=("app.py", "LAWS.laws", "proofs.laws")):
    d = Path(tempfile.mkdtemp())
    for src, dst in zip(("app.py", "LAWS.laws", "proofs.laws"), names):
        shutil.copy(EX / src, d / dst)
    return d


def test_project_discovers_files_without_config():
    d = make_project()
    (d / "util.py").write_text("print('not checked: does not import Nat from minilaws')\n", encoding="utf-8")
    (d / ".venv").mkdir()
    (d / ".venv" / "junk.laws").write_text("garbage", encoding="utf-8")
    ok, msg = check_project(d)
    assert ok, msg


def test_project_file_order_does_not_matter():
    # alphabetically: proofs, then laws, then code -- the checker sorts declarations itself
    d = make_project(names=("z_app.py", "m_LAWS.laws", "a_proofs.laws"))
    ok, msg = check_project(d)
    assert ok, msg


def test_project_failure_names_the_file():
    d = make_project()
    app = d / "app.py"
    app.write_text(app.read_text(encoding="utf-8").replace("m - 1) + 1", "m - 1)"), encoding="utf-8")
    ok, msg = check_project(d)
    assert not ok and "proofs.laws" in msg and "type mismatch" in msg


def test_project_toml_overrides_discovery():
    d = make_project()
    (d / "broken.laws").write_text("theorem nope : Eq zero (succ zero) := refl\n", encoding="utf-8")
    (d / "minilaws.toml").write_text('files = ["app.py", "LAWS.laws", "proofs.laws"]\n', encoding="utf-8")
    ok, msg = check_project(d)
    assert ok, msg


def test_project_without_laws_is_an_error():
    ok, msg = check_project(Path(tempfile.mkdtemp()))
    assert not ok and "no .laws files" in msg


def test_cli_check_command():
    good, bad = make_project(), make_project()
    (bad / "proofs.laws").write_text("", encoding="utf-8")
    run = lambda d: subprocess.run([sys.executable, str(ROOT / "minilaws.py"), "check", str(d)], capture_output=True, text=True)
    assert run(good).returncode == 0
    r = run(bad)
    assert r.returncode == 1 and "without proof" in r.stdout


if __name__ == "__main__":
    failed = 0
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            try:
                fn()
                print("ok  ", name)
            except Exception as e:
                failed += 1
                print("FAIL", name, "--", type(e).__name__, str(e).splitlines()[0] if str(e) else "")
    raise SystemExit(failed)
