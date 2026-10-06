"""Claude Code hook. `pre`: files with laws and minilaws.toml are human-owned, block edits to
them. `post`: after an edit to a checked file, re-check every proof; report failures to Claude.

A project is found the same way as for `minilaws check` and pytest: a folder with a
LAWS.laws or a minilaws.toml. No config is needed.

Bash can edit any file, and its command text says little (`sed -i`, scripts), so for Bash
the hooks look at the effect instead: `pre` records the project files, `post` compares.
A changed human-owned file is reported; any other change re-checks the proofs.

Fails closed: any unexpected error exits 2. Claude Code treats exit 1 as a non-blocking
error, so a crash would otherwise let the edit through unchecked.
"""
import hashlib
import json
import re
import sys
import tempfile
from pathlib import Path

HUMAN_OWNED = "is human-owned: change the code or the proofs, not the laws. If a law itself looks wrong, stop and ask the user."
BROKEN = "The laws no longer hold. Fix the code or the proof; do not weaken the law."


def find_root(start):
    for d in [start, *start.parents]:
        if any((d / m).is_file() for m in PROJECT_MARKERS):
            return d
    return None


def projects_near(cwd):
    """The project cwd is in, plus every project below it."""
    # ponytail: walks cwd on every Bash call; cache the project list if big repos make it slow
    return ({find_root(cwd)} | {find_root(d) or d for d in laws_dirs(cwd)}) - {None}


def has_laws(path):
    text = path.read_text(encoding="utf-8")
    try:
        return any(d[0] == "law" for d in parse_decls(text))
    except CheckError:
        return re.search(r"\blaw\b", text) is not None  # unparsable: assume it's the laws file


def human_owned(path):
    """Same rule as the checker (a file with a `law`), plus the config."""
    return path.name == "minilaws.toml" or (path.suffix == ".laws" and path.is_file() and has_laws(path))


def watched(root):
    return {p.resolve() for p in project_files(root)} | {(root / m).resolve() for m in PROJECT_MARKERS if (root / m).is_file()}


def snapshot(roots):
    return {str(p): [hashlib.sha256(p.read_bytes()).hexdigest(), human_owned(p)]
            for root in roots for p in watched(root) if p.is_file()}


def snapshot_file(event):
    key = re.sub(r"\W", "_", event.get("tool_use_id") or event.get("session_id") or "default")
    return Path(tempfile.gettempdir()) / "minilaws-hook" / f"{key}.json"


def check(roots):
    for root in sorted(roots):
        ok, msg = check_project(root)
        if not ok:
            print(f"{msg}\n\n{BROKEN}", file=sys.stderr)
            return 2
    return 0


def bash(mode, event, cwd):
    roots = projects_near(cwd)
    store = snapshot_file(event)
    if mode == "pre":
        store.parent.mkdir(exist_ok=True)
        store.write_text(json.dumps(snapshot(roots)), encoding="utf-8")
        return 0
    if not store.is_file():
        return check(roots)  # no record of the files before: at least re-check the proofs
    before = json.loads(store.read_text(encoding="utf-8"))
    store.unlink()
    after = snapshot(roots)
    changed = [p for p in before.keys() | after.keys() if before.get(p, [None])[0] != after.get(p, [None])[0]]
    owned = sorted(Path(p).name for p in changed if before.get(p, [None, False])[1])
    if owned:
        print(f"{', '.join(owned)} {HUMAN_OWNED} This command changed it: restore it (e.g. `git checkout`).",
              file=sys.stderr)
        return 2
    return check(roots) if changed else 0


def main(mode):
    event = json.load(sys.stdin)
    cwd = Path(event.get("cwd") or ".").resolve()
    if event.get("tool_name") == "Bash":
        return bash(mode, event, cwd)
    path = event.get("tool_input", {}).get("file_path")
    if not path:
        return 0
    target = (cwd / path).resolve()
    root = find_root(target.parent)
    if root is None:
        return 0
    if mode == "pre":
        if human_owned(target):
            print(f"{target.name} {HUMAN_OWNED}", file=sys.stderr)
            return 2
        return 0
    if target not in watched(root) and target.suffix != ".laws":
        return 0
    return check([root])


if __name__ == "__main__":
    try:
        # imported here so a broken install also fails closed
        sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
        from minilaws import PROJECT_MARKERS, CheckError, check_project, laws_dirs, parse_decls, project_files
        code = main(sys.argv[1])
    except Exception as e:
        print(f"minilaws hook failed ({type(e).__name__}: {e}); treating the edit as rejected. "
              "Fix the cause (e.g. minilaws.toml), or ask the user.", file=sys.stderr)
        code = 2
    sys.exit(code)
