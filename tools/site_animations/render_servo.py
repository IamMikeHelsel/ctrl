"""Classical IBVS vs depth-decoupled servoing under a 160 degree roll error."""
from __future__ import annotations

import shutil
import tempfile
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
import common as C  # noqa: E402
import mujoco  # noqa: E402
from PIL import Image  # noqa: E402

import servo_sim as sv  # noqa: E402

OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("servo_roll.gif")
FR = Path(tempfile.gettempdir()) / "ctrl_frames_servo"
SW = 470                       # width of the 3D panel
INTRO, OUTRO = 18, 50
XS = {"ibvs": -0.55, "dec": 0.55}
MARK = [(0.18, 0.83, 0.75), (0.98, 0.75, 0.14), (0.98, 0.44, 0.52), (0.38, 0.65, 0.98)]
MARK_PIL = [tuple(int(255 * v) for v in c) for c in MARK]


def scene_xml() -> str:
    marks = ""
    for name, x in XS.items():
        marks += f'<geom type="box" pos="{x} 0 0.002" size="0.23 0.23 0.002" material="board"/>'
        for i, (px, py, _) in enumerate(sv.PTS):
            marks += f'<geom type="cylinder" pos="{x + px} {py} 0.006" size="0.035 0.003" material="mk{i}"/>'
    rigs = ""
    for name, acc in (("ibvs", "rose"), ("dec", "teal")):
        rigs += f"""
    <body name="{name}" mocap="true" pos="0 0 2">
      <geom type="box" size="0.07 0.05 0.04" pos="0 0 -0.045" material="shell"/>
      <geom type="cylinder" size="0.03 0.02" pos="0 0 0.005" material="lens"/>
      <geom type="box" size="0.072 0.052 0.006" pos="0 0 -0.02" material="{acc}"/>
      <geom type="box" size="0.012 0.03 0.006" pos="0.05 0 -0.09" material="{acc}"/>
    </body>"""
    return f"""
<mujoco>
  <visual>
    <global offwidth="1920" offheight="1080"/>
    <quality shadowsize="4096" offsamples="8"/>
    <headlight ambient="0.3 0.31 0.34" diffuse="0.38 0.38 0.4" specular="0.1 0.1 0.1"/>
    <map znear="0.02" zfar="40"/>
  </visual>
  <asset>
    <texture name="sky" type="skybox" builtin="gradient" rgb1="0.1 0.13 0.18" rgb2="0.03 0.04 0.06" width="512" height="512"/>
    <texture name="grid" type="2d" builtin="checker" rgb1="0.12 0.14 0.18" rgb2="0.115 0.135 0.175" mark="edge" markrgb="0.22 0.27 0.34" width="512" height="512"/>
    <material name="floor" texture="grid" texrepeat="30 30" reflectance="0.1"/>
    <material name="board" rgba="0.05 0.06 0.08 1" specular="0.2"/>
    <material name="shell" rgba="0.84 0.86 0.9 1" specular="0.6"/>
    <material name="lens" rgba="0.08 0.09 0.11 1" specular="0.9" shininess="0.9"/>
    <material name="teal" rgba="0.18 0.83 0.75 1" emission="0.4"/>
    <material name="rose" rgba="0.98 0.44 0.52 1" emission="0.4"/>
    <material name="pole" rgba="0.3 0.33 0.38 1"/>
    <material name="mk0" rgba="0.18 0.83 0.75 1" emission="0.6"/>
    <material name="mk1" rgba="0.98 0.75 0.14 1" emission="0.6"/>
    <material name="mk2" rgba="0.98 0.44 0.52 1" emission="0.6"/>
    <material name="mk3" rgba="0.38 0.65 0.98 1" emission="0.6"/>
  </asset>
  <worldbody>
    <light pos="-1 -2 4" dir="0.2 0.4 -1" diffuse="0.7 0.7 0.72" castshadow="true"/>
    <geom type="plane" size="10 10 0.1" material="floor"/>
    {marks}
    {rigs}
  </worldbody>
</mujoco>"""


def mat2quat(R):
    q = np.zeros(4)
    mujoco.mju_mat2Quat(q, R.ravel())
    return q


def time_map(fi_sim, n_frames):
    """Slow motion at the start where IBVS retreats, then speed up. Returns sim time."""
    u = fi_sim / n_frames
    # piecewise: first 55% of frames cover 0..0.9 s, rest covers 0.9..4.0 s
    if u < 0.55:
        return 0.9 * (u / 0.55)
    return 0.9 + 3.1 * C.ease((u - 0.55) / 0.45)


def image_panel(dr, x0, y0, size, rows, k, s_star, col, title, f_lab, f_small):
    C.panel(dr, (x0, y0, x0 + size, y0 + size + 22), a=0.9)
    C.text(dr, (x0 + 10, y0 + 7), title, f_lab, col)
    cx, cy, sc = x0 + size / 2, y0 + 20 + size / 2, size * 1.9
    # image frame
    dr.rectangle((x0 + 8, y0 + 26, x0 + size - 8, y0 + size + 14), outline=C.alpha((38, 50, 68), 1))
    for (x, y), c in zip(s_star, MARK_PIL):
        X, Y = cx + x * sc, cy + y * sc
        dr.ellipse((X - 7, Y - 7, X + 7, Y + 7), outline=C.alpha(c, 0.55), width=1)
    for i, c in enumerate(MARK_PIL):
        pts = [(cx + rows[j]["s"][i][0] * sc, cy + rows[j]["s"][i][1] * sc) for j in range(0, k + 1, 10)]
        if len(pts) > 1:
            dr.line(pts, fill=C.alpha(c, 0.55), width=2)
        x, y = rows[k]["s"][i]
        X, Y = cx + x * sc, cy + y * sc
        dr.ellipse((X - 4, Y - 4, X + 4, Y + 4), fill=C.alpha(c, 1))


def main() -> None:
    runs = {"ibvs": sv.simulate("ibvs"), "dec": sv.simulate("decoupled")}
    s_star = runs["ibvs"][1]
    max_ibvs = max(r["depth"] for r in runs["ibvs"][0])

    m = mujoco.MjModel.from_xml_string(scene_xml())
    d = mujoco.MjData(m)
    r = mujoco.Renderer(m, C.H, SW)
    cam = mujoco.MjvCamera()
    cam.lookat[:] = [0.0, 0.0, 1.3]
    cam.elevation = -5
    mid = {n: m.body(n).mocapid[0] for n in XS}

    sim_frames = 150
    total = INTRO + sim_frames + OUTRO
    if FR.exists():
        shutil.rmtree(FR)
    FR.mkdir(parents=True)
    f_title, f_sub, f_lab, f_small, f_mono = C.font(22, "SemiBold"), C.font(13), C.font(12, "SemiBold"), C.font(11), C.mono(10)
    for fi in range(total):
        sf = min(max(fi - INTRO, 0), sim_frames)
        t = time_map(sf, sim_frames)
        k = min(int(t / sv.DT), len(runs["ibvs"][0]) - 1)
        prog = fi / total
        cam.azimuth = 90 + 14 * np.sin(2 * np.pi * prog * 0.5)
        cam.distance = 5.4
        for n, (rows, _) in runs.items():
            row = rows[k]
            d.mocap_pos[mid[n]] = row["p"] + np.array([XS[n], 0, 0])
            d.mocap_quat[mid[n]] = mat2quat(row["R"])
        mujoco.mj_forward(m, d)
        r.update_scene(d, cam)
        for n, (rows, _) in runs.items():
            cp = rows[k]["p"] + np.array([XS[n], 0, 0])
            for P, c in zip(sv.PTS, MARK):
                C.add_arrow(r.scene, cp, P + np.array([XS[n], 0, 0.008]), (*c, 0.35), width=0.003, kind="capsule")
        scene_img = Image.fromarray(r.render())
        img = Image.new("RGB", (C.W, C.H), C.BG)
        img.paste(scene_img, (0, 0))
        layer, dr = C.compose(img)

        ta = C.ease(fi / 10)
        C.text(dr, (20, 18), "Roll without retreat", f_title, a=ta)
        C.text(dr, (20, 48), "Both cameras must turn 160° and close from 2.2 m to 1.0 m.", f_sub, C.MUTED, ta)
        speed = f"{0.9 / (0.55 * sim_frames / C.FPS):.2f}× speed" if t < 0.9 else "speeding up"
        C.text(dr, (SW - 14, C.H - 18), f"{speed}   t = {t:0.2f} s", f_mono, C.MUTED, 0.9, anchor="ra")

        for n, col, lab in (("ibvs", C.ROSE, "classical IBVS"), ("dec", C.TEAL, "depth decoupled")):
            row = runs[n][0][k]
            cp = row["p"] + np.array([XS[n], 0, 0])
            pp = C.project(r.scene, cp + np.array([0, 0, 0.22]), w=SW)
            txt = f"{lab}  ·  {row['depth']:.2f} m"
            w = dr.textlength(txt, font=f_lab) + 22
            off = pp is None or pp[1] < 92
            if off:
                txt = "↑ " + txt
                w += 12
            X = (pp[0] if pp else SW / 4) + (-w / 2 - 14 if n == "ibvs" else w / 2 + 14)
            X = min(max(X, w / 2 + 8), SW - w / 2 - 8)
            Y = 92 if off else pp[1] + 14
            C.panel(dr, (X - w / 2, Y - 12, X + w / 2, Y + 12), a=0.9, radius=12, outline=C.alpha(col, 0.9))
            C.text(dr, (X, Y), txt, f_lab, col, anchor="mm")

        # what each camera sees
        C.text(dr, (SW + 16, 18), "WHAT EACH CAMERA SEES", f_small, C.MUTED)
        ps = 168
        image_panel(dr, SW + 16, 38, ps, runs["ibvs"][0], k, s_star, C.ROSE, "classical IBVS", f_lab, f_small)
        image_panel(dr, SW + 16, 38 + ps + 30, ps, runs["dec"][0], k, s_star, C.TEAL, "depth decoupled", f_lab, f_small)
        C.text(dr, (SW + 16 + ps + 10, 64), "IBVS pulls", f_small, C.MUTED)
        C.text(dr, (SW + 16 + ps + 10, 80), "features in", f_small, C.MUTED)
        C.text(dr, (SW + 16 + ps + 10, 96), "straight lines,", f_small, C.MUTED)
        C.text(dr, (SW + 16 + ps + 10, 112), "so the camera", f_small, C.MUTED)
        C.text(dr, (SW + 16 + ps + 10, 128), "backs away.", f_small, C.MUTED)
        C.text(dr, (SW + 16 + ps + 10, 64 + ps + 30), "Rotation and", f_small, C.MUTED)
        C.text(dr, (SW + 16 + ps + 10, 80 + ps + 30), "depth handled", f_small, C.MUTED)
        C.text(dr, (SW + 16 + ps + 10, 96 + ps + 30), "separately.", f_small, C.MUTED)

        if fi >= INTRO + sim_frames - 4:
            a = C.ease((fi - (INTRO + sim_frames - 4)) / 12)
            bx, by = 20, C.H - 124
            C.panel(dr, (bx, by, bx + 300, by + 96), a=0.9 * a)
            C.text(dr, (bx + 14, by + 10), f"IBVS climbed to {max_ibvs:.1f} m first", C.font(15, "SemiBold"), C.ROSE, a)
            C.text(dr, (bx + 14, by + 36), "Depth-decoupled stayed inside [1.0, 2.2] m.", f_small, C.TEXT, a)
            C.text(dr, (bx + 14, by + 54), "Proved: rotating about the optical axis", f_small, C.TEXT, a)
            C.text(dr, (bx + 14, by + 70), "never changes depth to the plane.", f_small, C.TEXT, a)

        C.flatten(img, layer).save(FR / f"f{fi:04d}.png")

    size = C.encode_gif(FR, OUT)
    print(OUT, f"{size / 1e6:.2f} MB", total, "frames", "IBVS max", round(max_ibvs, 2))


if __name__ == "__main__":
    main()
