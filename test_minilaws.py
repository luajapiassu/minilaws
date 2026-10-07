import shutil
import subprocess
import sys
import tempfile
import textwrap
import random
from dataclasses import replace
from itertools import product
from pathlib import Path

from minilaws import App, CheckError, Const, Env, Lam, Meta, Pi, Sort, Var, apply, instantiate, spine, check_project, check_source, main, read_source, translate_python

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


def test_instantiate_matches_textbook_definition():
    # instantiate is trusted. Reference: body[0 := arg] as shift(-1) . subst . shift(+1),
    # the obvious-but-slow version it replaced. repr() also compares Var.explicit.
    def shift(t, d, cut=0):
        match t:
            case Var(i):
                return replace(t, i=i + d) if i >= cut else t
            case Pi(_, a, b) | Lam(_, a, b):
                return replace(t, dom=a and shift(a, d, cut), body=shift(b, d, cut + 1))
            case App(f, a):
                return App(shift(f, d, cut), shift(a, d, cut))
        return t

    def subst(t, j, s):
        match t:
            case Var(i):
                return s if i == j else t
            case Pi(_, a, b) | Lam(_, a, b):
                return replace(t, dom=a and subst(a, j, s), body=subst(b, j + 1, shift(s, 1)))
            case App(f, a):
                return App(subst(f, j, s), subst(a, j, s))
        return t

    def term(depth, binders):
        r = rng.random()
        if depth == 0 or r < 0.25:
            return rng.choice([Var(rng.randrange(binders + 3), rng.random() < 0.3), Const("c"), Sort(0), Meta(0)])
        if r < 0.5:
            return App(term(depth - 1, binders), term(depth - 1, binders))
        dom = term(depth - 1, binders)
        if rng.random() < 0.5:
            return Pi("x", dom, term(depth - 1, binders + 1))
        return Lam("x", None if rng.random() < 0.2 else dom, term(depth - 1, binders + 1), rng.random() < 0.3)

    rng = random.Random(0)
    for _ in range(3000):
        body, arg = term(rng.randrange(7), 1), term(rng.randrange(5), 0)
        assert repr(instantiate(body, arg)) == repr(shift(subst(body, 0, shift(arg, 1)), -1)), (body, arg)


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
inductive Stack (A : Type 0) : Type 0 where
  | empty : Stack A
  | push : A -> Stack A -> Stack A
def length : {A : Type 0} -> Stack A -> Nat :=
  fun xs => Stack.rec (fun _ => Nat) zero (fun _ _ ih => succ ih) xs
def append : {A : Type 0} -> Stack A -> Stack A -> Stack A :=
  fun {A} xs ys => Stack.rec (fun _ => Stack A) ys (fun x _ ih => push x ih) xs
"""


def test_user_inductive_computes():
    check_source(LIST + "theorem t : Eq (length (push zero (push zero empty))) (succ (succ zero)) := refl")


def test_law_about_user_inductive_by_induction():
    check_source(LIST + """
law length_append : {A : Type 0} -> (xs ys : Stack A) -> Eq (length (append xs ys)) (add (length ys) (length xs))
proof length_append := fun {A} xs ys =>
  Stack.rec (fun l => Eq (length (append l ys)) (add (length ys) (length l))) refl (fun x l ih => cong succ ih) xs
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


# ---------- large elimination (T.rec1) ----------

IS_ZERO = "def IsZero : Nat -> Type 0 := fun n => Nat.rec1 (fun _ => Type 0) Unit (fun _ _ => Empty) n\n"


def test_large_elimination_proves_constructors_differ():
    check_source(IS_ZERO + "theorem zero_ne_succ : (n : Nat) -> Not (Eq zero (succ n)) := fun n h => Eq.subst IsZero h tt")


def test_large_elimination_on_user_inductive():
    check_source("""
inductive Coin : Type 0 where
  | heads : Coin
  | tails : Coin
def IsHeads : Coin -> Type 0 := fun c => Coin.rec1 (fun _ => Type 0) Unit Empty c
theorem heads_ne_tails : Not (Eq heads tails) := fun h => Eq.subst IsHeads h tt
""")


def test_prelude_bool_true_ne_false():
    check_source("""
def IsTrue : Bool -> Type 0 := fun b => Bool.rec1 (fun _ => Type 0) Empty Unit b
theorem true_ne_false : Not (Eq true false) := fun h => Eq.subst IsTrue h tt
""")


def test_large_elimination_proves_nothing_false():
    rejects(IS_ZERO + "theorem bad : Not (Eq zero zero) := fun h => Eq.subst IsZero h tt", "type mismatch")
    rejects(IS_ZERO + "theorem bad : Empty := Eq.subst IsZero (@refl Nat zero) tt", "type mismatch")
    # the motive may land in Type 1, no higher
    rejects("def T : Nat -> Type 1 := fun n => Nat.rec1 (fun _ => Type 1) (Type 0) (fun _ _ => Type 0) n", "type mismatch")


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


TRANSLATED = PY_ADD + py("""
    def mul(n: Nat, m: Nat) -> Nat:
        if m == 0:
            return 0
        return add(mul(n, m - 1), n)

    def pow2(m: Nat) -> Nat:
        if m == 0:
            return 1
        return add(pow2(m - 1), pow2(m - 1))

    def pred(m: Nat) -> Nat:
        if m == 0:
            return m
        return m - 1

    def tri(m: Nat) -> Nat:
        if m == 0:
            return m + 2
        return add(tri(m - 1), m)

    def poly(a: Nat, b: Nat) -> Nat:
        return add(mul(a, a + 1), pred(b) + 3)

    def eq(a: Nat, b: Nat) -> bool:
        return a == b

    def cmp(a: Nat, b: Nat) -> list[bool]:
        return [a != b, a < b, a <= b, a > b, a >= b]

    def logic(p: bool, q: bool) -> list[bool]:
        return [not p, p and q, p or q, p and q or not p, True, False]

    def max2(a: Nat, b: Nat) -> Nat:
        if a < b:
            return b
        return a

    def clamp(a: Nat, b: Nat) -> Nat:
        return 3 if a > 3 else a + 1

    def sum(xs: list[Nat]) -> Nat:
        if not xs:
            return 0
        return add(xs[0], sum(xs[1:]))

    def small(xs: list[Nat]) -> list[Nat]:
        if not xs:
            return xs
        return [xs[0]] + small(xs[1:]) if xs[0] < 2 else small(xs[1:])

    def cat(xs: list[Nat], ys: list[Nat]) -> list[Nat]:
        if not xs:
            return ys
        return [xs[0]] + cat(xs[1:], ys)

    def has(xs: list[Nat], k: Nat) -> bool:
        if not xs:
            return False
        return xs[0] == k or has(xs[1:], k)

    def wrap(a: Nat) -> list[list[Nat]]:
        return [[], [a, a + 1]]

    LIMIT: Nat = 2
    TOP: Nat = LIMIT + 1

    def below(a: Nat) -> bool:
        return a < LIMIT

    def seeded(xs: list[Nat]) -> list[Nat]:
        return cat([TOP, 0], xs)

    def shove(n: Nat, m: Nat) -> Nat:
        if m == 0:
            return n
        return shove(n + 1, m - 1)

    def rev(xs: list[Nat], acc: list[Nat]) -> list[Nat]:
        if not xs:
            return acc
        return rev(xs[1:], [xs[0]] + acc)

    def nest(n: Nat, a: Nat, b: Nat) -> Nat:
        if n == 0:
            return add(a, b)
        return nest(n - 1, nest(n - 1, b, a), a + 1)
    """)

# argument kinds: N = Nat, B = bool, L = list[Nat]
FUNCTIONS = {"add": "NN", "mul": "NN", "pow2": "N", "pred": "N", "tri": "N", "poly": "NN", "eq": "NN",
             "cmp": "NN", "logic": "BB", "max2": "NN", "clamp": "NN", "sum": "L", "small": "L",
             "cat": "LL", "has": "LN", "wrap": "N", "below": "N",
             "seeded": "L", "shove": "NN", "rev": "LL", "nest": "NNN"}


def test_translation_computes_what_python_computes():
    # The translator is trusted, so test it differentially: the kernel, used as an
    # interpreter, must agree with the Python that actually runs.
    env = check_source(translate_python(TRANSLATED))
    ns = {}
    exec(TRANSLATED, ns)

    def term(v):
        if isinstance(v, bool):
            return Const("true" if v else "false")
        if isinstance(v, int):
            return Const("zero") if v == 0 else App(Const("succ"), term(v - 1))
        out = App(Const("nil"), Const("Nat"))
        for x in reversed(v):
            out = apply(Const("cons"), [Const("Nat"), term(x), out])
        return out

    def value(t):
        head, args = spine(env.whnf(t))
        match head.name:
            case "zero":
                return 0
            case "succ":
                return 1 + value(args[0])
            case "true" | "false":
                return head.name == "true"
            case "nil":
                return []
            case "cons":
                return [value(args[1])] + value(args[2])
        raise AssertionError(f"not a value: {t}")

    samples = {"N": range(4), "B": (False, True), "L": ([], [0], [3, 1], [2, 0, 5, 1])}
    for name, kinds in FUNCTIONS.items():
        for args in product(*(samples[k] for k in kinds)):
            assert value(apply(Const(name), [term(a) for a in args])) == ns[name](*args), (name, args)


def test_law_about_python_list_function():
    src = py("""
        def cat(xs: list[Nat], ys: list[Nat]) -> list[Nat]:
            if not xs:
                return ys
            return [xs[0]] + cat(xs[1:], ys)
        """)
    check_source(translate_python(src) + """
theorem cong : {A B : Type 0} -> {a b : A} -> (f : A -> B) -> Eq a b -> Eq (f a) (f b) :=
  fun {A B a b} f h => Eq.subst (fun x => Eq (f a) (f x)) h refl
law cat_nil : (xs : List Nat) -> Eq (cat xs nil) xs
proof cat_nil := fun xs =>
  List.rec (fun l => Eq (cat l nil) l) refl (fun x l ih => cong (cons x) ih) xs
""")


def test_law_about_accumulator_by_generalized_induction():
    # the motive is a function type (`(n : Nat) -> ...`), so the recursor takes one more argument
    src = PY_ADD + py("""
        def shove(n: Nat, m: Nat) -> Nat:
            if m == 0:
                return n
            return shove(n + 1, m - 1)
        """)
    check_source(translate_python(src) + """
theorem cong : {A B : Type 0} -> {a b : A} -> (f : A -> B) -> Eq a b -> Eq (f a) (f b) :=
  fun {A B a b} f h => Eq.subst (fun x => Eq (f a) (f x)) h refl
theorem trans : {A : Type 0} -> {a b c : A} -> Eq a b -> Eq b c -> Eq a c :=
  fun {A a b c} h k => Eq.subst (fun x => Eq a x) k h
theorem succ_add : (n m : Nat) -> Eq (add (succ n) m) (succ (add n m)) :=
  fun n m => Nat.rec (fun m => Eq (add (succ n) m) (succ (add n m))) refl (fun m ih => cong succ ih) m
law shove_add : (n m : Nat) -> Eq (shove n m) (add n m)
proof shove_add := fun n m =>
  Nat.rec (fun m => (n : Nat) -> Eq (shove n m) (add n m))
    (fun n => refl) (fun m ih n => trans (ih (succ n)) (succ_add n m)) m n
""")


def test_python_type_errors_are_rejected_by_the_kernel():
    # the translator doesn't track types; comparing lists still can't get through
    rejects(translate_python(py("""
        def f(xs: list[Nat], ys: list[Nat]) -> bool:
            return xs == ys
        """)), "type mismatch")


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
    def f(n: Nat, m: Nat) -> Nat:  # recursion on m, but m lands in n's place
        if m == 0:
            return n
        return f(m - 1, n)
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
    """
    def f(xs: list[Nat]) -> Nat:  # xs[0] only after `if not xs`, where xs isn't empty
        return xs[0]
    """,
    """
    def f(xs: list[Nat]) -> list[Nat]:  # only xs[0] and xs[1:]
        if not xs:
            return xs
        return f(xs[2:])
    """,
    """
    def f(n: Nat) -> Nat:  # recursion needs the structural test, not any condition
        if n < 3:
            return 0
        return f(n - 1)
    """,
    """
    def f(a: Nat, b: Nat, c: Nat) -> bool:  # chained comparison
        return a < b < c
    """,
    """
    def f(xs: list[int]) -> Nat:  # elements must be Nat too
        return 0
    """,
    """
    def f(xs: list) -> Nat:  # element type required
        return 0
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


def test_law_cannot_depend_on_code_outside_python_or_its_own_file():
    # AI unmarks app.py (so its buggy add isn't checked) and redefines add in proofs.laws
    d = make_project()
    (d / "app.py").write_text("def add(n, m):\n    return n\n", encoding="utf-8")
    with open(d / "proofs.laws", "a", encoding="utf-8") as f:
        f.write("\n" + ADD)
    ok, msg = check_project(d)
    assert not ok and "law add_zero" in msg and "'add'" in msg, msg


def test_law_cannot_depend_on_a_type_from_a_proof_file():
    # an empty type defined by the AI would make a law about it vacuous
    d = make_project()
    (d / "LAWS.laws").write_text("law all_empty : (x : Thing) -> Eq x x\n", encoding="utf-8")
    (d / "proofs.laws").write_text("inductive Thing : Type 0 where\nproof all_empty := fun x => refl\n", encoding="utf-8")
    ok, msg = check_project(d)
    assert not ok and "'Thing'" in msg, msg


def test_law_may_use_defs_from_its_own_file():
    d = make_project()
    with open(d / "LAWS.laws", "a", encoding="utf-8") as f:
        f.write("def double : Nat -> Nat := fun n => add n n\nlaw double_zero : Eq (double zero) zero\n")
    with open(d / "proofs.laws", "a", encoding="utf-8") as f:
        f.write("proof double_zero := refl\n")
    ok, msg = check_project(d)
    assert ok, msg


def test_python_rejects_imports_other_than_minilaws():
    # the checker would verify one add while Python runs another
    try:
        translate_python("from evil import add\n")
    except CheckError as e:
        assert "unsupported" in str(e)
        return
    raise AssertionError("translated a foreign import")


def test_python_rejects_calls_to_functions_not_defined_earlier_in_the_file():
    src = py("""
        def double(n: Nat) -> Nat:
            return add(n, n)
        """)
    try:
        translate_python(src)
    except CheckError as e:
        assert "unsupported" in str(e) and "add" in str(e)
        return
    raise AssertionError("translated a call to an unknown function")


def test_python_syntax_error_is_rejected():
    d = make_project()
    (d / "app.py").write_text("from minilaws import Nat\ndef add(\n", encoding="utf-8")
    ok, msg = check_project(d)
    assert not ok and "app.py" in msg, msg


def test_large_literal_is_checked():
    # unary Nat: n + 2000 is 2000 nested succs, checked by the kernel in conv
    d = make_project()
    with open(d / "app.py", "a", encoding="utf-8") as f:
        f.write("\n\ndef big(n: Nat) -> Nat:\n    return n + 2000\n")
    with open(d / "LAWS.laws", "a", encoding="utf-8") as f:
        f.write("law big_add : (n : Nat) -> Eq (big n) (add n (big zero))\n")
    with open(d / "proofs.laws", "a", encoding="utf-8") as f:
        f.write("proof big_add := fun n => refl\n")
    ok, msg = check_project(d)
    assert ok, msg


def test_huge_literal_is_rejected_not_a_crash():
    d = make_project()
    with open(d / "app.py", "a", encoding="utf-8") as f:
        f.write("\n\ndef big(n: Nat) -> Nat:\n    return n + 20000\n")
    ok, msg = check_project(d)
    assert not ok and "app.py" in msg and "above 10000" in msg, msg


def test_deep_hand_written_term_is_rejected_not_a_crash():
    d = make_project()
    with open(d / "proofs.laws", "a", encoding="utf-8") as f:
        f.write("theorem deep : Nat := " + "succ (" * 100_000 + "zero" + ")" * 100_000 + "\n")
    ok, msg = check_project(d)
    assert not ok and "too deep" in msg, msg


def test_missing_file_is_rejected_not_a_crash():
    d = make_project()
    (d / "minilaws.toml").write_text('files = ["app.py", "LAWS.laws", "gone.laws"]\n', encoding="utf-8")
    ok, msg = check_project(d)
    assert not ok and "gone.laws" in msg, msg


def test_def_and_theorem_order_across_files_does_not_matter():
    # a_ sorts first but needs z_'s code and lemmas
    d = make_project(names=("z_app.py", "LAWS.laws", "a_proofs.laws"))
    proofs = (d / "a_proofs.laws").read_text(encoding="utf-8")
    lemmas, rest = proofs.split("-- By computation")
    (d / "a_proofs.laws").write_text("--" + rest +"def twice : Nat -> Nat := fun n => add n n\n", encoding="utf-8")
    (d / "z_lemmas.laws").write_text(lemmas, encoding="utf-8")
    ok, msg = check_project(d)
    assert ok, msg


def test_nested_project_is_checked_on_its_own():
    outer = make_project()
    shutil.copytree(make_project(), outer / "sub")  # same names, separate project
    assert check_project(outer)[0] and check_project(outer / "sub")[0]


def test_dir_named_env_is_checked_but_real_venvs_are_skipped():
    d = make_project()
    for name, marker in (("env", False), ("myvenv", True)):
        (d / name).mkdir()
        (d / name / "x.laws").write_text(f"law nope_{name} : Eq zero (succ zero)\n", encoding="utf-8")
        if marker:
            (d / name / "pyvenv.cfg").write_text("", encoding="utf-8")
    ok, msg = check_project(d)
    assert not ok and "nope_env" in msg and "nope_myvenv" not in msg, msg


def test_at_works_on_local_variables():
    check_source("theorem t : (f : {x : Nat} -> Nat) -> Nat := fun f => @f zero")


def test_cli_check_command():
    good, bad = make_project(), make_project()
    (bad / "proofs.laws").write_text("", encoding="utf-8")
    run = lambda d: subprocess.run([sys.executable, str(ROOT / "minilaws.py"), "check", str(d)], capture_output=True, text=True)
    assert run(good).returncode == 0
    r = run(bad)
    assert r.returncode == 1 and "without proof" in r.stdout


def test_python_constant_is_checked_and_usable():
    src = py("""
        K: Nat = 3
        K1: Nat = K + 1
        def is_k(n: Nat) -> bool:
            return n == K
        """)
    ns = {"Nat": int}
    exec(src, ns)
    assert ns["is_k"](3) and ns["K1"] == 4
    check_source(translate_python(src) + """
        theorem t : Eq (is_k (succ (succ (succ zero)))) true := refl
        theorem u : Eq K1 (succ (succ (succ (succ zero)))) := refl
        """)


def test_python_constant_must_be_annotated_and_not_redefined():
    try:
        translate_python("K = 3\n")
        raise AssertionError("translated an unannotated constant")
    except CheckError as e:
        assert "unsupported" in str(e), str(e)
    rejects(translate_python("K: Nat = 3\nK: Nat = 4\n"), "already declared")
    try:  # a list is mutable: the main block could change it after it was checked
        translate_python("XS: list[Nat] = [1]\n")
        raise AssertionError("translated a list constant")
    except CheckError as e:
        assert "unsupported" in str(e), str(e)


def test_python_main_block_is_skipped():
    src = PY_ADD + py("""
        if __name__ == "__main__":
            x = add(2, 3)
            print(x)
        """)
    assert translate_python(src) == translate_python(PY_ADD)


def test_python_main_block_cannot_rebind_checked_names():
    # the checker would verify one add while the script runs another
    for body in ("add = max", "def add(a, b): return 0", "from evil import add",
                 "for add in []: pass", "import evil as add", "del add", "(add := 0)",
                 "from evil import *", "try: pass\n    except Exception as add: pass",
                 "match 0:\n        case add: pass", "match []:\n        case [*add]: pass",
                 "match {}:\n        case {**add}: pass"):
        src = PY_ADD + f'if __name__ == "__main__":\n    {body}\n'
        try:
            translate_python(src)
        except CheckError as e:
            assert "unsupported" in str(e) and ("add" in str(e) or "*" in str(e)), str(e)
            continue
        raise AssertionError(f"main block rebinding add was translated: {body}")


def test_python_main_block_must_be_last_and_plain():
    for src in (
        'if __name__ == "__main__":\n    pass\n' + PY_ADD,
        PY_ADD + 'if __name__ == "__main__":\n    pass\nelse:\n    pass\n',
        PY_ADD + 'if __name__ != "__main__":\n    pass\n',
    ):
        try:
            translate_python(src)
        except CheckError as e:
            assert "unsupported" in str(e), str(e)
            continue
        raise AssertionError(f"translated:\n{src}")


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
