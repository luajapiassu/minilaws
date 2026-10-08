"""Renders the README's traffic-light GIFs from examples/traffic, checked by minilaws.

    python media/traffic.py

Three versions of examples/traffic/app.py: as committed, the AI's first try at
"give the avenue a longer green", and its retry. Each is checked by minilaws (the
script asserts the expected verdict), then its avenue/street/next_phase functions
drive the simulation, so a crash in a GIF is a crash the code really allows.
Needs Pillow (not a minilaws dependency).
"""
import importlib.util
import shutil
import sys
import tempfile
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from minilaws import check_project  # noqa: E402

LONGER_AVENUE = ("""    if phase == 0:
        return GREEN
    return YELLOW if phase == 1 else RED""", """    if phase <= 1:
        return GREEN
    return YELLOW if phase == 2 else RED""")
FIVE_PHASES = ("    if phase == 3:\n        return 0", "    if phase == 4:\n        return 0")
STREET_LATER = ("""    if phase == 2:
        return GREEN
    return YELLOW if phase == 3 else RED""", """    if phase == 3:
        return GREEN
    return YELLOW if phase == 4 else RED""")
PROOF_5 = ("  refl) p) p) p) p", """  Nat.rec (fun k => Eq (crash (succ (succ (succ (succ k))))) false) refl (fun p _ =>
  refl) p) p) p) p) p""")

CAPTIONS = {"law": "minilaws: OK", "bug": "without minilaws: merged", "kept": "with minilaws: retried, OK"}
VERSIONS = {
    "law": {},                                                 # as committed
    "bug": {"app.py": [LONGER_AVENUE, FIVE_PHASES]},           # forgot to move the street
    "kept": {"app.py": [LONGER_AVENUE, FIVE_PHASES, STREET_LATER], "proofs.laws": [PROOF_5]},
}

GREEN, YELLOW, RED = 0, 1, 2
W = 320
ROAD = (130, 190)          # both roads span this band
STOP = ROAD[0] - 6         # stop line, same distance on both roads
CAR_L, CAR_W, SPEED, GAP = 26, 14, 3, 10
SPAWN = {"avenue": 36, "street": 4}  # tick offsets in a 40-tick cycle
TICKS = {GREEN: 60, YELLOW: 36}  # yellow outlasts crossing the box: (60 + 26) / 3 < 36
COLORS = {GREEN: "#2ecc71", YELLOW: "#f1c40f", RED: "#e74c3c"}


def build(name, edits, tmp):
    d = tmp / name
    shutil.copytree(ROOT / "examples" / "traffic", d)
    for fname, subs in edits.items():
        p = d / fname
        text = p.read_text(encoding="utf-8")
        for old, new in subs:
            assert old in text, (name, fname, old)
            text = text.replace(old, new)
        p.write_text(text, encoding="utf-8")
    _, verdict = check_project(d)
    spec = importlib.util.spec_from_file_location(f"traffic_{name}", d / "app.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod, verdict


class Car:
    def __init__(self, road):
        self.road, self.pos = road, -CAR_L  # pos = rear edge along the road

    def rect(self):
        a, b = self.pos, self.pos + CAR_L
        # drive on the right: eastbound avenue in the lower lane, southbound street in the left one
        lane = (ROAD[1] - 8 - CAR_W, ROAD[1] - 8) if self.road == "avenue" else (ROAD[0] + 8, ROAD[0] + 8 + CAR_W)
        return (a, lane[0], b, lane[1]) if self.road == "avenue" else (lane[0], a, lane[1], b)


def simulate(app, ticks):
    """Yield (phase, cars, crash) per tick. Cars enter only on green; once in, they go."""
    phase, left = 0, None
    cars = []
    spawn = SPAWN
    for t in range(ticks):
        colors = {"avenue": app.avenue(phase), "street": app.street(phase)}
        if left is None:
            left = TICKS[GREEN if YELLOW not in colors.values() else YELLOW]
        for road in spawn:
            if t % 40 == spawn[road] and all(c.pos > GAP for c in cars if c.road == road):
                cars.append(Car(road))
        for road in ("avenue", "street"):
            ahead = None
            for c in sorted((c for c in cars if c.road == road), key=lambda c: -c.pos):
                front = c.pos + CAR_L
                nxt = c.pos + SPEED
                if front <= STOP < front + SPEED and colors[road] != GREEN:
                    nxt = STOP - CAR_L
                if ahead is not None:
                    nxt = min(nxt, ahead.pos - GAP - CAR_L)
                c.pos = max(c.pos, nxt)
                ahead = c
        cars = [c for c in cars if c.pos < W]
        crash = next(((a, s) for a in cars if a.road == "avenue" for s in cars if s.road == "street"
                      if overlap(a.rect(), s.rect())), None)
        yield phase, colors, cars, crash
        if crash:
            return
        left -= 1
        if left == 0:
            phase, left = app.next_phase(phase), None


def overlap(r, s):
    return r[0] < s[2] and s[0] < r[2] and r[1] < s[3] and s[1] < r[3]


FONT = ImageFont.load_default(size=13)
BIG = ImageFont.load_default(size=26)


def light(d, x, y, color):
    d.rounded_rectangle((x, y, x + 16, y + 44), 4, fill="#222")
    for i, c in enumerate((RED, YELLOW, GREEN)):
        d.ellipse((x + 3, y + 3 + 13 * i, x + 13, y + 13 + 13 * i), fill=COLORS[c] if c == color else "#444")


def frame(phase, colors, cars, crash, caption):
    im = Image.new("RGB", (W, W + 28), "#6ab04c")
    d = ImageDraw.Draw(im)
    d.rectangle((0, ROAD[0], W, ROAD[1]), fill="#555")
    d.rectangle((ROAD[0], 0, ROAD[1], W), fill="#555")
    for k in range(0, W, 24):  # lane dashes, outside the box
        if not ROAD[0] - 12 < k < ROAD[1]:
            d.line((k, 160, k + 12, 160), fill="#ddd", width=2)
            d.line((160, k, 160, k + 12), fill="#ddd", width=2)
    d.line((STOP, ROAD[0], STOP, ROAD[1]), fill="white", width=3)
    d.line((ROAD[0], STOP, ROAD[1], STOP), fill="white", width=3)
    light(d, STOP - 24, ROAD[1] + 6, colors["avenue"])
    light(d, ROAD[1] + 6, STOP - 50, colors["street"])
    d.text((8, ROAD[1] + 8), "avenue", fill="white", font=FONT)
    d.text((ROAD[1] + 26, 8), "street", fill="white", font=FONT)
    for c in cars:
        d.rounded_rectangle(c.rect(), 3, fill="#3498db" if c.road == "avenue" else "#9b59b6", outline="#111")
    if crash:
        a, s = crash[0].rect(), crash[1].rect()
        cx, cy = (max(a[0], s[0]) + min(a[2], s[2])) / 2, (max(a[1], s[1]) + min(a[3], s[3])) / 2
        for r, col in ((30, "#e67e22"), (18, "#f1c40f")):
            d.regular_polygon((cx, cy, r), 8, rotation=22, fill=col)
        d.text((W / 2, 40), "CRASH", fill="#c0392b", font=BIG, anchor="mm", stroke_width=3, stroke_fill="white")
    d.rectangle((0, W, W, W + 28), fill="#111")
    d.text((8, W + 7), caption, fill="#eee", font=FONT)
    d.text((W - 8, W + 7), f"phase {phase}", fill="#888", font=FONT, anchor="ra")
    return im


def render(name, app, verdict, ticks):
    frames = []
    for i, (phase, colors, cars, crash) in enumerate(simulate(app, ticks)):
        if i % 2 == 0 or crash:  # 2 ticks per frame keeps the file small
            frames.append(frame(phase, colors, cars, crash, verdict))
    durations = [66] * len(frames)
    durations[-1] = 2500
    out = ROOT / "media" / f"traffic_{name}.gif"
    frames[0].save(out, save_all=True, append_images=frames[1:], duration=durations, loop=0, optimize=True)
    return out


def main():
    with tempfile.TemporaryDirectory() as tmp:
        for name, edits in VERSIONS.items():
            app, verdict = build(name, edits, Path(tmp))
            assert verdict.startswith("REJECTED") == (name == "bug"), (name, verdict)
            crashed = any(c for *_, c in simulate(app, 600))
            assert crashed == (name == "bug"), (name, crashed)
            out = render(name, app, CAPTIONS[name], 600)
            print(f"{out.relative_to(ROOT)}: {verdict.splitlines()[0]}")


if __name__ == "__main__":
    main()
