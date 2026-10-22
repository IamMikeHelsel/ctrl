"""Braking shield animation: same planner, same robot, with and without the closed-form shield."""
from __future__ import annotations

import math
import shutil
import tempfile
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
import common as C  # noqa: E402
import mujoco  # noqa: E402
from PIL import Image  # noqa: E402

import brake_scene as bs  # noqa: E402

OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("brake_shield.gif")
FR = Path(tempfile.gettempdir()) / "ctrl_frames_brake"
SLOW = 0.25           # playback speed relative to real time
INTRO, OUTRO = 20, 50  # frames


def main() -> None:
    safe, raw = bs.simulate(True), bs.simulate(False)
    dt = 0.002
    n_sim = int(round(1.35 / dt))
    sim_frames = int(round(n_sim * dt / SLOW * C.FPS))
    impact_k = next(k for k, o in enumerate(raw) if o["contact"])
    impact_v = raw[impact_k]["v"][0]
    stop_x = max(o["qpos"][0] for o in safe[:n_sim])
    min_fz = min(min(f[2] for f in o["forces"].values()) for o in safe[:n_sim])

    m = mujoco.MjModel.from_xml_string(bs.visual_xml())
    d = mujoco.MjData(m)
    r = mujoco.Renderer(m, C.H, C.W)
    cam = mujoco.MjvCamera()
    cam.lookat[:] = [2.2, 0.25, 0.25]
    cam.elevation = -14

    lanes = {"safe": (-0.85, safe), "raw": (0.85, raw)}
    ids = {n: m.body(n).mocapid[0] for n in lanes}
    jnt = {n: [m.joint(f"{n}_j{i}").qposadr[0] for i in range(4)] for n in lanes}

    f_title, f_sub, f_lab, f_small = C.font(22, "SemiBold"), C.font(13), C.font(12, "SemiBold"), C.font(11)
    f_mono, f_big = C.mono(10), C.font(18, "SemiBold")

    if FR.exists():
        shutil.rmtree(FR)
    FR.mkdir(parents=True)
    total = INTRO + sim_frames + OUTRO
    flash = 0.0
    for fi in range(total):
        sf = min(max(fi - INTRO, 0), sim_frames)
        k = min(int(round(sf / C.FPS * SLOW / dt)), n_sim - 1)
        prog = fi / total
        cam.azimuth = 150 + 14 * C.ease(prog)
        cam.distance = 5.4 - 0.3 * C.ease(prog)

        tele = {}
        for name, (y, run) in lanes.items():
            o = run[k]
            qp = o["qpos"]
            d.mocap_pos[ids[name]] = [qp[0], y + qp[1], qp[2]]
            d.mocap_quat[ids[name]] = qp[3:7]
            for a in jnt[name]:
                d.qpos[a] = qp[0] / 0.09
            tele[name] = o
        mujoco.mj_forward(m, d)
        r.update_scene(d, cam)

        # Ground reaction arrows at the four wheels
        for name, (y, run) in lanes.items():
            o = tele[name]
            col = (0.18, 0.95, 0.85, 0.9) if name == "safe" else (1.0, 0.45, 0.55, 0.9)
            for (ex, ey), f in o["forces"].items():
                if f is None or o["com"][2] < 0.3:
                    continue
                base = np.array([o["qpos"][0] + ex * 0.25, y + o["qpos"][1] + ey * 0.33, 0.004])
                tip = base + f / 420.0
                C.add_arrow(r.scene, base, tip, col, width=0.02)
        img = Image.fromarray(r.render())
        layer, dr = C.compose(img)

        # Title block
        ta = C.ease(fi / 10)
        C.text(dr, (24, 18), "Braking shield", f_title, a=ta)
        C.text(dr, (24, 48), "Same robot, same planner, 3 m/s toward a dock edge. One runs the closed-form filter.", f_sub, C.MUTED, ta)
        C.text(dr, (C.W - 24, 22), f"{SLOW:.2f}× speed   t = {k * dt:0.2f} s", f_mono, C.MUTED, 0.9, anchor="ra")
        C.text(dr, (C.W - 24, C.H - 18), "MuJoCo 3.16 · 40 kg · CoM 0.45 m · μ = 0.6", f_mono, C.MUTED, 0.7, anchor="ra")

        # Floating labels
        for name, (y, _run) in lanes.items():
            o = tele[name]
            p = C.project(r.scene, [o["com"][0], y + o["com"][1], o["com"][2] + 0.62])
            if p is None:
                continue
            col = C.TEAL if name == "safe" else C.ROSE
            label = "with ctrl shield" if name == "safe" else ("planner only" if k < impact_k else f"planner only · off the edge at {impact_v:.1f} m/s")
            w = dr.textlength(label, font=f_lab) + 22
            p = (min(max(p[0], w / 2 + 8), C.W - w / 2 - 8), max(p[1], 104))
            C.panel(dr, (p[0] - w / 2, p[1] - 12, p[0] + w / 2, p[1] + 12), a=0.85, radius=14, outline=C.alpha(col, 0.9))
            C.text(dr, (p[0], p[1]), label, f_lab, col, anchor="mm")

        # HUD for the shielded lane
        o = tele["safe"]
        hx, hy = 24, C.H - 106
        C.panel(dr, (hx, hy, hx + 290, hy + 84), a=0.82)
        C.text(dr, (hx + 12, hy + 8), "SHIELD TELEMETRY", f_small, C.TEAL)
        C.text(dr, (hx + 12, hy + 27), f"speed {o['v'][0]:5.2f} m/s", f_mono, C.TEXT)
        C.text(dr, (hx + 150, hy + 27), f"margin h {max(o['h'], 0):5.3f} m", f_mono, C.TEXT)
        C.text(dr, (hx + 12, hy + 44), "blend toward brake  λ", f_mono, C.MUTED)
        C.bar(dr, hx + 160, hy + 46, 116, 8, o["lam"], C.TEAL)
        fz = o["forces"]
        front = (fz[(1, 1)][2] + fz[(1, -1)][2]) / 2
        rear = (fz[(-1, 1)][2] + fz[(-1, -1)][2]) / 2
        C.text(dr, (hx + 12, hy + 61), f"wheel load  front {front:5.1f} N  rear {rear:5.1f} N", f_mono, C.MUTED)

        # Outro callouts
        if fi >= INTRO + sim_frames - 8:
            a = C.ease((fi - (INTRO + sim_frames - 8)) / 14)
            bx, by = C.W - 300, 62
            C.panel(dr, (bx, by, C.W - 24, by + 146), a=0.88 * a)
            C.text(dr, (bx + 14, by + 10), "What the shield guaranteed", f_lab, C.TEAL, a)
            lines = [
                f"front wheels stop {1000 * (bs.X_LIMIT - stop_x):.0f} mm from the limit",
                f"rear wheels never unloaded (min {min_fz:.1f} N)",
                "every wheel force inside the friction cone",
                "zero net torque about the CoM, by proof",
                "one closed-form call per tick, no solver",
            ]
            for i, s in enumerate(lines):
                C.text(dr, (bx + 14, by + 34 + i * 21), "•  " + s, f_small, C.TEXT, a)

        C.flatten(img, layer).save(FR / f"f{fi:04d}.png")

    size = C.encode_gif(FR, OUT)
    print(OUT, f"{size / 1e6:.2f} MB", total, "frames")


if __name__ == "__main__":
    main()
