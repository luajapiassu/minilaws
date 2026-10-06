"""The pytest plugin, loaded explicitly so these tests don't depend on `pip install -e .`."""
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).parent
EX = ROOT / "examples"


def project():
    d = Path(tempfile.mkdtemp())
    for f in ("app.py", "LAWS.laws", "proofs.laws"):
        shutil.copy(EX / f, d / f)
    return d


def pytest_in(d, *args):
    env = os.environ | {"PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1", "PYTHONPATH": str(ROOT)}
    return subprocess.run(
        [sys.executable, "-m", "pytest", str(d), "-q", "-p", "no:cacheprovider", "-p", "pytest_minilaws", *args],
        capture_output=True, text=True, cwd=d, env=env,
    )


def test_laws_become_a_passing_test():
    r = pytest_in(project())
    assert r.returncode == 0 and "1 passed" in r.stdout, r.stdout


def test_broken_law_fails_pytest_with_the_reason():
    d = project()
    app = d / "app.py"
    app.write_text(app.read_text(encoding="utf-8").replace("m - 1) + 1", "m - 1)"), encoding="utf-8")
    r = pytest_in(d)
    assert r.returncode == 1 and "type mismatch" in r.stdout, r.stdout


def test_deleting_the_laws_file_fails_pytest():
    # the leftover proofs no longer have laws to prove
    d = project()
    (d / "LAWS.laws").unlink()
    r = pytest_in(d)
    assert r.returncode == 1 and "no such law" in r.stdout, r.stdout


def test_against_option_catches_a_removed_law():
    # without it, deleting a law together with its proof still passes: the rest is proved
    d = project()
    git = lambda *a: subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *a], cwd=d, check=True, capture_output=True)
    git("init", "-q")
    git("add", "-A")
    git("commit", "-qm", "base")
    for f, cut in (("LAWS.laws", "law add_assoc"), ("proofs.laws", "proof add_assoc")):
        text = (d / f).read_text(encoding="utf-8")
        (d / f).write_text(text[: text.index(cut)], encoding="utf-8")
    assert pytest_in(d).returncode == 0
    r = pytest_in(d, "--minilaws-against=HEAD")
    assert r.returncode == 1 and "law add_assoc: removed" in r.stdout, r.stdout


def test_warns_when_testpaths_skip_the_laws():
    # otherwise narrowing collection silently turns the laws off
    d = project()
    (d / "tests").mkdir()
    (d / "tests" / "test_ok.py").write_text("def test_ok():\n    pass\n", encoding="utf-8")
    (d / "pytest.ini").write_text("[pytest]\ntestpaths = tests\n", encoding="utf-8")
    env = os.environ | {"PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1", "PYTHONPATH": str(ROOT)}
    r = subprocess.run([sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider", "-p", "pytest_minilaws"],
                       capture_output=True, text=True, cwd=d, env=env)
    assert r.returncode == 0 and "laws not collected" in r.stdout and d.name in r.stdout, r.stdout
