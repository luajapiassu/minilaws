"""The pytest plugin: needs the package installed (`pip install -e .`) so pytest finds its entry point."""
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

EX = Path(__file__).parent / "examples"


def project():
    d = Path(tempfile.mkdtemp())
    for f in ("app.py", "LAWS.laws", "proofs.laws"):
        shutil.copy(EX / f, d / f)
    return d


def pytest_in(d):
    return subprocess.run(
        [sys.executable, "-m", "pytest", str(d), "-q", "-p", "no:cacheprovider"],
        capture_output=True, text=True, cwd=d,
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
