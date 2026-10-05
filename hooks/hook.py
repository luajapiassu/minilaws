"""Claude Code hook. `pre`: laws files are human-owned, block edits to them.
`post`: after an edit to a checked file, re-check every proof; report failures to Claude.

Projects opt in with a minilaws.toml next to (or above) their files:
    files = ["app.py", "LAWS.laws", "proofs.laws"]   # checked in this order
    laws = ["LAWS.laws"]                              # Claude may not edit these
"""
import json
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from minilaws import check_files  # noqa: E402


def find_root(start):
    for d in [start, *start.parents]:
        if (d / "minilaws.toml").is_file():
            return d
    return None


def main(mode):
    event = json.load(sys.stdin)
    path = event.get("tool_input", {}).get("file_path") or event.get("tool_input", {}).get("notebook_path")
    if not path:
        return 0
    target = (Path(event.get("cwd") or ".") / path).resolve()
    root = find_root(target.parent)
    if root is None:
        return 0
    cfg = tomllib.loads((root / "minilaws.toml").read_text(encoding="utf-8"))
    resolve = lambda names: [(root / n).resolve() for n in names]

    if mode == "pre":
        if target in resolve(cfg.get("laws", [])):
            print(
                f"{target.name} is human-owned: change the code or the proofs, not the laws. "
                "If a law itself looks wrong, stop and ask the user.",
                file=sys.stderr,
            )
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
    sys.exit(main(sys.argv[1]))
