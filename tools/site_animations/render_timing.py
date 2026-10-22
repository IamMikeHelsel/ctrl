"""Per-tick compute time: SOCP force allocation (Clarabel) vs the closed-form C99 shield tick."""
from __future__ import annotations

import json
import math
import shutil
import tempfile
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
import common as C  # noqa: E402
from PIL import Image  # noqa: E402

OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("timing.gif")
FR = Path(tempfile.gettempdir()) / "ctrl_frames_timing"
B = Path(__file__).parent / "bench"
INTRO, MAIN, OUTRO = 14, 132, 54

solver = np.array(json.load(open(B / "socp.json"))["ns"], float)
iters = np.array(json.load(open(B / "socp.json"))["iters"])
kern = np.loadtxt(B / "tick.txt")
N = min(len(solver), len(kern))

# chart geometry
X0, Y0, X1, Y1 = 70, 96, 540, 396
LO, HI = 1.0, 7.0          # log10 ns: 10 ns .. 10 ms
WINDOW = 400               # ticks visible


def ymap(ns):
    v = (math.log10(max(ns, 10 ** LO)) - LO) / (HI - LO)
    return Y1 - v * (Y1 - Y0)


def ticks_at(fi):
    """How many ticks have been revealed: slow at first, then faster."""
    u = min(max((fi - INTRO) / MAIN, 0.0), 1.0)
    return int(6 + (N - 6) * (u ** 2.2))


def main() -> None:
    if FR.exists():
        shutil.rmtree(FR)
    FR.mkdir(parents=True)
    f_title, f_sub, f_lab, f_small, f_mono = C.font(22, "SemiBold"), C.font(13), C.font(12, "SemiBold"), C.font(11), C.mono(10)
    total = INTRO + MAIN + OUTRO
    for fi in range(total):
        img = Image.new("RGB", (C.W, C.H), C.BG)
        layer, dr = C.compose(img)
        ta = C.ease(fi / 10)
        C.text(dr, (24, 18), "The clock doesn't care how hard the state is", f_title, a=ta)
        C.text(dr, (24, 48), "Same 4-wheel force allocation, every tick: an SOCP solver vs the closed-form kernel.", f_sub, C.MUTED, ta)

        # axes
        C.panel(dr, (X0 - 54, Y0 - 16, X1 + 14, Y1 + 30), a=0.6)
        for e, lab in ((1, "10 ns"), (2, "100 ns"), (3, "1 µs"), (4, "10 µs"), (5, "100 µs"), (6, "1 ms"), (7, "10 ms")):
            y = ymap(10 ** e)
            dr.line((X0, y, X1, y), fill=C.alpha((38, 50, 68), 0.8), width=1)
            C.text(dr, (X0 - 8, y), lab, f_mono, C.MUTED, anchor="rm")
        yd = ymap(1e6)
        for x in range(X0, X1, 10):
            dr.line((x, yd, x + 5, yd), fill=C.alpha(C.AMBER, 0.9), width=1)
        C.text(dr, (X1 - 4, yd - 4), "1 kHz loop budget", f_small, C.AMBER, anchor="rd")
        C.text(dr, ((X0 + X1) / 2, Y1 + 16), "control ticks →", f_small, C.MUTED, anchor="mm")

        n = ticks_at(fi)
        lo = max(0, n - WINDOW)
        for i in range(lo, n):
            x = X0 + (X1 - X0) * (i - lo) / WINDOW
            for arr, col, rad in ((solver, C.ROSE, 2.2), (kern, C.TEAL, 2.0)):
                y = ymap(arr[i])
                fresh = 1.0 if i > n - 6 else 0.75
                dr.ellipse((x - rad, y - rad, x + rad, y + rad), fill=C.alpha(col, fresh))

        # legend + live stats
        sx = X1 + 30
        s_seen, k_seen = solver[:n], kern[:n]
        C.text(dr, (sx, Y0 - 8), "SOCP SOLVER (Clarabel)", f_small, C.ROSE)
        C.text(dr, (sx, Y0 + 10), f"median   {np.median(s_seen) / 1e3:7.1f} µs", f_mono, C.TEXT)
        C.text(dr, (sx, Y0 + 26), f"worst    {s_seen.max() / 1e3:7.1f} µs", f_mono, C.TEXT)
        C.text(dr, (sx, Y0 + 42), f"iterations   {iters[:n].min()} to {iters[:n].max()}", f_mono, C.TEXT)
        C.text(dr, (sx, Y0 + 58), f"over budget  {(s_seen > 1e6).sum()} ticks", f_mono, C.TEXT)

        C.text(dr, (sx, Y0 + 96), "CTRL C99 KERNEL", f_small, C.TEAL)
        C.text(dr, (sx, Y0 + 114), f"median   {np.median(k_seen):7.1f} ns", f_mono, C.TEXT)
        C.text(dr, (sx, Y0 + 130), "iterations   0", f_mono, C.TEXT)
        C.text(dr, (sx, Y0 + 146), "loops        none", f_mono, C.TEXT)
        C.text(dr, (sx, Y0 + 162), "heap         0 bytes", f_mono, C.TEXT)
        C.text(dr, (sx, Y0 + 194), f"tick {n:4d} of {N}", f_mono, C.MUTED)

        if fi >= INTRO + MAIN - 4:
            a = C.ease((fi - (INTRO + MAIN - 4)) / 12)
            ratio = np.median(solver) / np.median(kern)
            bx, by = sx - 10, Y0 + 220
            C.panel(dr, (bx, by, C.W - 20, by + 96), a=0.92 * a, outline=C.alpha(C.TEAL, 0.6 * a))
            C.text(dr, (bx + 12, by + 10), f"~{float(f'{ratio:.2g}'):,.0f}× faster at the median", C.font(15, "SemiBold"), C.TEAL, a)
            C.text(dr, (bx + 12, by + 36), "More useful: the work doesn't depend on", f_small, C.TEXT, a)
            C.text(dr, (bx + 12, by + 52), "the state, so the worst case is a fixed", f_small, C.TEXT, a)
            C.text(dr, (bx + 12, by + 68), "op count you can put in a safety case.", f_small, C.TEXT, a)

        C.text(dr, (24, C.H - 18), f"Measured on one Xeon core in a cloud VM, {N} random states. Kernel tick also runs the safety filter.",
               f_small, C.MUTED, 0.8)
        C.flatten(img, layer).save(FR / f"f{fi:04d}.png")

    size = C.encode_gif(FR, OUT, colors=96)
    print(OUT, f"{size / 1e6:.2f} MB", total, "frames")


if __name__ == "__main__":
    main()
