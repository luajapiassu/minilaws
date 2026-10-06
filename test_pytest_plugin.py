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


def pytest_in(d):
    env = os.environ | {"PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1", "PYTHONPATH": str(ROOT)}
    return subprocess.run(
        [sys.executable, "-m", "pytest", str(d), "-q", "-p", "no:cacheprovider", "-p", "pytest_minilaws"],
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
