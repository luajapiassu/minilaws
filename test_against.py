"""`check --against REF`: the laws at a trusted git ref are the challenge (like Lean's
comparator). Every law there must still exist with the same statement, and everything the
statement depends on must be unchanged: spec defs/types in full, code by signature and file."""
import shutil
import subprocess
import tempfile
from pathlib import Path

from minilaws import check_project

EX = Path(__file__).parent / "examples"


def git(d, *args):
    subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args], cwd=d, check=True, capture_output=True)


def repo():
    """A git repo whose HEAD is the example project: the trusted base."""
    d = Path(tempfile.mkdtemp())
    for f in ("app.py", "LAWS.laws", "proofs.laws"):
        shutil.copy(EX / f, d / f)
    git(d, "init", "-q")
    git(d, "add", "-A")
    git(d, "commit", "-qm", "base")
    return d


def edit(path, old, new):
    text = path.read_text(encoding="utf-8")
    assert old in text, old
    path.write_text(text.replace(old, new), encoding="utf-8")


def against_head(d):
    return check_project(d, against="HEAD")


def test_unchanged_project_passes():
    ok, msg = against_head(repo())
    assert ok, msg


def test_weakened_law_is_rejected():
    # add_comm now only claims commutativity with zero: easy to prove, much weaker
    d = repo()
    edit(d / "LAWS.laws", "law add_comm : (a b : Nat) -> Eq (add a b) (add b a)",
         "law add_comm : (a : Nat) -> Eq (add a zero) (add zero a)")
    edit(d / "proofs.laws", "proof add_comm := fun a b =>", "proof add_comm := fun a => symm (zero_add a)\ntheorem old_comm : (a b : Nat) -> Eq (add a b) (add b a) := fun a b =>")
    ok, msg = against_head(d)
    assert not ok and "add_comm" in msg and "statement changed" in msg, msg
    # the human approving it sees both statements, as the kernel reads them (#5, #9)
    assert "was: (a : Nat) -> (b : Nat) -> Eq Nat (add a b) (add b a)" in msg, msg
    assert "now: (a : Nat) -> Eq Nat (add a zero) (add zero a)" in msg, msg


def test_removed_law_is_rejected():
    d = repo()
    edit(d / "LAWS.laws", "law add_assoc : (a b c : Nat) -> Eq (add (add a b) c) (add a (add b c))\n", "")
    edit(d / "proofs.laws", "proof add_assoc :=", "theorem add_assoc : (a b c : Nat) -> Eq (add (add a b) c) (add a (add b c)) :=")
    ok, msg = against_head(d)
    assert not ok and "add_assoc" in msg and "removed" in msg, msg


def test_new_law_is_fine():
    d = repo()
    with open(d / "LAWS.laws", "a", encoding="utf-8") as f:
        f.write("law add_one : (n : Nat) -> Eq (add n (succ zero)) (succ n)\n")
    with open(d / "proofs.laws", "a", encoding="utf-8") as f:
        f.write("proof add_one := fun n => refl\n")
    ok, msg = against_head(d)
    assert ok, msg


def test_cosmetic_changes_are_fine():
    d = repo()
    edit(d / "LAWS.laws", "law add_zero : (n : Nat) -> Eq (add n zero) n", "-- renamed binder\nlaw add_zero : (k : Nat) -> Eq (add k zero) k")
    edit(d / "app.py", "    if m == 0:", '    """Peano addition."""\n    if m == 0:')
    ok, msg = against_head(d)
    assert ok, msg


def test_code_moving_to_another_file_is_rejected():
    # the old file stops being checked (marker gone, still buggy at runtime) and a correct copy lives elsewhere
    d = repo()
    shutil.copy(d / "app.py", d / "fixed.py")
    (d / "app.py").write_text("def add(n, m):\n    return n\n", encoding="utf-8")
    ok, msg = against_head(d)
    assert not ok and "'add'" in msg and "fixed.py" in msg and "app.py" in msg, msg


def test_changed_spec_def_is_rejected():
    d = repo()
    with open(d / "LAWS.laws", "a", encoding="utf-8") as f:
        f.write("def double : Nat -> Nat := fun n => add n n\nlaw double_zero : Eq (double zero) zero\n")
    with open(d / "proofs.laws", "a", encoding="utf-8") as f:
        f.write("proof double_zero := refl\n")
    git(d, "commit", "-qam", "double")
    edit(d / "LAWS.laws", "fun n => add n n", "fun n => add n zero")
    ok, msg = against_head(d)
    assert not ok and "double_zero" in msg and "'double'" in msg, msg


def test_base_without_laws_is_fine():
    d = Path(tempfile.mkdtemp())
    git(d, "init", "-q")
    (d / "README").write_text("x", encoding="utf-8")
    git(d, "add", "-A")
    git(d, "commit", "-qm", "empty")
    for f in ("app.py", "LAWS.laws", "proofs.laws"):
        shutil.copy(EX / f, d / f)
    ok, msg = against_head(d)
    assert ok, msg


def test_project_in_a_subfolder():
    d = repo()
    sub = Path(tempfile.mkdtemp()) / "outer"
    shutil.copytree(d, sub / "proj", ignore=shutil.ignore_patterns(".git"))
    git(sub, "init", "-q")
    git(sub, "add", "-A")
    git(sub, "commit", "-qm", "base")
    edit(sub / "proj" / "LAWS.laws", "law add_zero : (n : Nat) -> Eq (add n zero) n\n", "")
    edit(sub / "proj" / "proofs.laws", "proof add_zero := fun n => refl\n", "")
    ok, msg = check_project(sub / "proj", against="HEAD")
    assert not ok and "add_zero" in msg and "removed" in msg, msg
