import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

ROOT = Path(__file__).parent
HOOK = ROOT / "hooks" / "hook.py"
CONFIG = 'files = ["app.py", "LAWS.laws", "proofs.laws"]\n'


def project(config=CONFIG):
    d = Path(tempfile.mkdtemp())
    for f in ("app.py", "LAWS.laws", "proofs.laws"):
        shutil.copy(ROOT / "examples" / f, d / f)
    if config:
        (d / "minilaws.toml").write_text(config, encoding="utf-8")
    return d


def run(mode, d, file_path=None, tool="Edit"):
    tool_input = {"file_path": file_path} if file_path else {"command": "sed -i ..."}
    event = {"hook_event_name": mode, "cwd": str(d), "tool_name": tool, "tool_input": tool_input,
             "session_id": "s", "tool_use_id": f"t-{d.name}"}
    r = subprocess.run([sys.executable, str(HOOK), mode], input=json.dumps(event), capture_output=True, text=True)
    return r.returncode, r.stderr


def test_no_project_is_a_noop():
    d = Path(tempfile.mkdtemp())
    (d / "app.py").write_text("garbage(", encoding="utf-8")
    assert run("post", d, str(d / "app.py")) == (0, "")


def test_zero_config_pre_blocks_editing_laws():
    # LAWS.laws marks a project, like for `minilaws check` and pytest
    d = project(config=None)
    code, err = run("pre", d, str(d / "LAWS.laws"))
    assert code == 2 and "human-owned" in err


def test_zero_config_post_reports_broken_law():
    d = project(config=None)
    app = d / "app.py"
    app.write_text(app.read_text(encoding="utf-8").replace("m - 1) + 1", "m - 1)"), encoding="utf-8")
    code, err = run("post", d, str(app))
    assert code == 2 and "type mismatch" in err


def test_pre_blocks_any_file_with_laws():
    # the checker treats every file with a `law` as human-owned; so does the hook
    d = project(config=None)
    (d / "more.laws").write_text("law z : Eq zero zero\n", encoding="utf-8")
    code, err = run("pre", d, str(d / "more.laws"))
    assert code == 2 and "human-owned" in err


def test_pre_allows_editing_proofs():
    d = project(config=None)
    assert run("pre", d, str(d / "proofs.laws"))[0] == 0


def bash(d, change):
    """Run the Bash hooks around `change`, the way Claude Code would."""
    assert run("pre", d, tool="Bash")[0] == 0
    change()
    return run("post", d, tool="Bash")


def test_bash_editing_laws_is_reported():
    # issue #3: hooks see the effect of a Bash command, not its text
    d = project(config=None)
    law = d / "LAWS.laws"
    code, err = bash(d, lambda: law.write_text(law.read_text(encoding="utf-8") + "-- weaker\n", encoding="utf-8"))
    assert code == 2 and "LAWS.laws" in err and "human-owned" in err


def test_bash_breaking_code_is_reported():
    d = project(config=None)
    app = d / "app.py"
    code, err = bash(d, lambda: app.write_text(
        app.read_text(encoding="utf-8").replace("m - 1) + 1", "m - 1)"), encoding="utf-8"))
    assert code == 2 and "type mismatch" in err


def test_bash_finds_projects_below_cwd():
    root = Path(tempfile.mkdtemp())
    d = project(config=None)
    shutil.move(d, root / "sub")
    law = root / "sub" / "LAWS.laws"
    code, err = bash(root, lambda: law.unlink())
    assert code == 2 and "LAWS.laws" in err


def test_bash_without_changes_passes_even_if_a_human_edited_laws_before():
    d = project(config=None)
    law = d / "LAWS.laws"
    law.write_text(law.read_text(encoding="utf-8") + "-- human note\n", encoding="utf-8")
    assert bash(d, lambda: None) == (0, "")


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


# ---------- the command in hooks.json: python3, else python, never both ----------

BASH = shutil.which("bash")
needs_bash = pytest.mark.skipif(BASH is None or "system32" in BASH.lower(), reason="needs a POSIX bash (not WSL's)")


def hook_command(shims):
    """Run the `pre` command from hooks.json with only the given fake interpreters on PATH.
    shims: {name: (exit code for `-c ''`, exit code when run on the hook)}. Returns
    (exit code, stderr, the shims that ran the hook)."""
    d = Path(tempfile.mkdtemp())
    log = d / "log"
    for name, (probe, code) in shims.items():
        (d / name).write_text(f'#!/bin/sh\n[ "$1" = -c ] && exit {probe}\necho {name} >> "{log.as_posix()}"\nexit {code}\n')
        (d / name).chmod(0o755)
    command = json.loads((ROOT / "hooks" / "hooks.json").read_text())["hooks"]["PreToolUse"][0]["hooks"][0]["command"]
    r = subprocess.run([BASH, "-c", command], capture_output=True, text=True,
                       env={"PATH": d.as_posix(), "CLAUDE_PLUGIN_ROOT": ROOT.as_posix()})
    return r.returncode, r.stderr, log.read_text().split() if log.exists() else []


@needs_bash
def test_hook_command_prefers_python3_and_runs_once():
    # python3 blocks the edit (exit 2): python must not run it a second time
    assert hook_command({"python3": (0, 2), "python": (0, 0)})[::2] == (2, ["python3"])


@needs_bash
def test_hook_command_falls_back_to_python():
    # macOS without python3 is the other way round; a broken python3 stub (Windows Store) likewise
    assert hook_command({"python": (0, 0)})[::2] == (0, ["python"])
    assert hook_command({"python3": (9009, 0), "python": (0, 0)})[::2] == (0, ["python"])


@needs_bash
def test_hook_command_without_python_fails_closed():
    code, err, ran = hook_command({})
    assert (code, ran) == (2, []) and "python" in err
