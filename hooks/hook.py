"""Claude Code hook. `pre`: laws files and minilaws.toml are human-owned, block edits to them.
`post`: after an edit to a checked file, re-check every proof; report failures to Claude.

Projects opt in with a minilaws.toml next to (or above) their files:
    files = ["app.py", "LAWS.laws", "proofs.laws"]   # the files to check
    laws = ["LAWS.laws"]                              # Claude may not edit these

Fails closed: any unexpected error exits 2. Claude Code treats exit 1 as a non-blocking
error, so a crash would otherwise let the edit through unchecked.
"""
import json
import sys
from pathlib import Path

HUMAN_OWNED = "is human-owned: change the code or the proofs, not the laws. If a law itself looks wrong, stop and ask the user."


def find_root(start):
    for d in [start, *start.parents]:
        if (d / "minilaws.toml").is_file():
            return d
    return None


def main(mode):
    import tomllib

    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from minilaws import check_files

    event = json.load(sys.stdin)
    path = event.get("tool_input", {}).get("file_path")
    if not path:
        return 0
    target = (Path(event.get("cwd") or ".") / path).resolve()
    root = find_root(target.parent)
    if root is None:
        return 0
    if mode == "pre" and target == (root / "minilaws.toml").resolve():
        print(f"{target.name} {HUMAN_OWNED}", file=sys.stderr)
        return 2
    cfg = tomllib.loads((root / "minilaws.toml").read_text(encoding="utf-8"))
    resolve = lambda names: [(root / n).resolve() for n in names]

    if mode == "pre":
        if target in resolve(cfg.get("laws", [])):
            print(f"{target.name} {HUMAN_OWNED}", file=sys.stderr)
            return 2
        return 0

    files = resolve(cfg.get("files", []))
    if target not in files:
        return 0
    ok, msg = check_files(files)
    if ok:
        return 0
    print(f"{msg}\n\nThe laws in {', '.join(cfg.get('laws', []))} no longer hold. "
          "Fix the code or the proof; do not weaken the law.", file=sys.stderr)
    return 2


if __name__ == "__main__":
    try:
        code = main(sys.argv[1])
    except Exception as e:
        print(f"minilaws hook failed ({type(e).__name__}: {e}); treating the edit as rejected. "
              "Fix the cause (e.g. minilaws.toml), or ask the user.", file=sys.stderr)
        code = 2
    sys.exit(code)
