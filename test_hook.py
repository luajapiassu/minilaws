import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).parent
HOOK = ROOT / "hooks" / "hook.py"
CONFIG = 'files = ["app.py", "LAWS.laws", "proofs.laws"]\nlaws = ["LAWS.laws"]\n'


def project(config=CONFIG):
    d = Path(tempfile.mkdtemp())
    for f in ("app.py", "LAWS.laws", "proofs.laws"):
        shutil.copy(ROOT / "examples" / f, d / f)
    if config:
        (d / "minilaws.toml").write_text(config, encoding="utf-8")
    return d


def run(mode, d, file_path, tool="Edit"):
    event = {"hook_event_name": mode, "cwd": str(d), "tool_name": tool, "tool_input": {"file_path": file_path}}
    r = subprocess.run([sys.executable, str(HOOK), mode], input=json.dumps(event), capture_output=True, text=True)
    return r.returncode, r.stderr


def test_no_config_is_a_noop():
    d = project(config=None)
    (d / "app.py").write_text("garbage(", encoding="utf-8")
    assert run("post", d, str(d / "app.py")) == (0, "")


def test_pre_blocks_editing_laws():
    d = project()
    code, err = run("pre", d, str(d / "LAWS.laws"))
    assert code == 2 and "human-owned" in err


def test_pre_blocks_editing_the_config():
    # otherwise LAWS.laws could be dropped from `laws` or `files`
    d = project()
    code, err = run("pre", d, "minilaws.toml")
    assert code == 2 and "human-owned" in err


def test_hook_fails_closed_on_unexpected_errors():
    # exit 1 is a non-blocking error for Claude Code: the edit would go through unchecked
    d = project(config="files = [\n")
    code, err = run("post", d, str(d / "app.py"))
    assert code == 2 and "minilaws hook failed" in err


def test_pre_allows_editing_code():
    d = project()
    assert run("pre", d, "app.py")[0] == 0  # relative paths resolve against cwd


def test_post_passes_when_laws_hold():
    d = project()
    assert run("post", d, str(d / "app.py")) == (0, "")


def test_post_reports_broken_law_to_claude():
    d = project()
    app = d / "app.py"
    app.write_text(app.read_text(encoding="utf-8").replace("m - 1) + 1", "m - 1)"), encoding="utf-8")
    code, err = run("post", d, str(app))
    assert code == 2 and "type mismatch" in err


def test_post_reports_unproved_law():
    d = project()
    (d / "proofs.laws").write_text("", encoding="utf-8")
    code, err = run("post", d, str(d / "proofs.laws"))
    assert code == 2 and "without proof" in err


def test_post_ignores_files_outside_the_project():
    d = project()
    (d / "app.py").write_text("garbage(", encoding="utf-8")
    (d / "notes.md").write_text("hi", encoding="utf-8")
    assert run("post", d, str(d / "notes.md")) == (0, "")


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
