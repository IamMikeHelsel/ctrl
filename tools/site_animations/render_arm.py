"""Septic (eta = -11) vs minimum-jerk: same arm, same path, same time, less winding heat."""
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

from ctrl.robotics.mujoco_benchmarks import ARM_6DOF_MJCF  # noqa: E402
from ctrl.robotics.trajectories import septic_a, septic_q, septic_v  # noqa: E402

OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("septic_arm.gif")
FR = Path(tempfile.gettempdir()) / "ctrl_frames_arm"
Q_T = np.array([1.25, -0.95, 1.15, -1.40, 1.10, -1.50])
T_MOVE, T_HOLD = 0.8, 0.3
R_ELEC, K_T = 0.45, 0.12
SLOW = 0.3
INTRO, OUTRO = 18, 54


def plan(eta, t):
    """Forward move, hold, return move."""
    if t < T_MOVE:
        s, sign, base = t / T_MOVE, 1.0, 0.0
    elif t < T_MOVE + T_HOLD:
        return Q_T.copy(), np.zeros(6), np.zeros(6)
    else:
        s, sign, base = min((t - T_MOVE - T_HOLD) / T_MOVE, 1.0), -1.0, 1.0
    q = Q_T * (base + sign * float(septic_q(eta, s)))
    v = Q_T * sign * float(septic_v(eta, s)) / T_MOVE
    a = Q_T * sign * float(septic_a(eta, s)) / T_MOVE**2
    return q, v, a


def simulate(eta):
    m = mujoco.MjModel.from_xml_string(ARM_6DOF_MJCF)
    d = mujoco.MjData(m)
    arm, damp = m.dof_armature[:6].copy(), m.dof_damping[:6].copy()
    dt = m.opt.timestep
    n = int(round((2 * T_MOVE + T_HOLD) / dt))
    rows, e_dyn = [], 0.0
    for k in range(n):
        qd, vd, ad = plan(eta, k * dt)
        acc = ad + 450.0 * (qd - d.qpos[:6]) + 35.0 * (vd - d.qvel[:6])
        d.qacc[:6] = acc
        tau = np.zeros(6)
        mujoco.mj_rne(m, d, 1, tau)
        tau += arm * acc + damp * d.qvel[:6]     # rotor inertia and viscous friction
        v_s, a_s = d.qvel[:6].copy(), d.qacc[:6].copy()
        d.qvel[:6] = 0.0
        d.qacc[:6] = 0.0
        g = np.zeros(6)
        mujoco.mj_rne(m, d, 0, g)
        d.qvel[:6], d.qacc[:6] = v_s, a_s
        p_joint = (R_ELEC / K_T**2) * (tau - g) ** 2
        e_dyn += float(p_joint.sum()) * dt
        rows.append(dict(t=k * dt, q=d.qpos[:6].copy(), p=p_joint, e=e_dyn))
        d.ctrl[:6] = tau
        mujoco.mj_step(m, d)
    return rows


def arm_xml(prefix: str, x: float, y: float, accent: str) -> str:
    def housing(i, euler):
        return (f'<geom name="{prefix}_h{i}" type="cylinder" size="0.058 0.05" euler="{euler}" '
                f'material="steel" contype="0" conaffinity="0"/>')
    return f"""
    <body pos="{x} {y} 0">
      <geom type="cylinder" size="0.12 0.05" pos="0 0 0.05" material="base"/>
      <geom type="cylinder" size="0.123 0.006" pos="0 0 0.1" material="{accent}"/>
      <body name="{prefix}1" pos="0 0 0.1">
        <joint name="{prefix}j1" type="hinge" axis="0 0 1"/>
        {housing(1, "0 0 0")}
        <geom type="capsule" fromto="0 0 0 0 0 0.25" size="0.045" material="shell"/>
        <body pos="0 0 0.25">
          <joint name="{prefix}j2" type="hinge" axis="0 1 0"/>
          {housing(2, "90 0 0")}
          <geom type="capsule" fromto="0 0 0 0.28 0 0" size="0.04" material="shell"/>
          <geom type="box" size="0.1 0.042 0.004" pos="0.14 0 0.035" material="{accent}"/>
          <body pos="0.28 0 0">
            <joint name="{prefix}j3" type="hinge" axis="0 1 0"/>
            {housing(3, "90 0 0")}
            <geom type="capsule" fromto="0 0 0 0.24 0 0" size="0.035" material="shell"/>
            <body pos="0.24 0 0">
              <joint name="{prefix}j4" type="hinge" axis="1 0 0"/>
              {housing(4, "0 90 0")}
              <geom type="capsule" fromto="0 0 0 0.16 0 0" size="0.03" material="shell"/>
              <body pos="0.16 0 0">
                <joint name="{prefix}j5" type="hinge" axis="0 1 0"/>
                {housing(5, "90 0 0")}
                <geom type="capsule" fromto="0 0 0 0.12 0 0" size="0.025" material="shell"/>
                <body pos="0.12 0 0">
                  <joint name="{prefix}j6" type="hinge" axis="0 0 1"/>
                  {housing(6, "0 0 0")}
                  <geom type="cylinder" pos="0 0 0.03" size="0.035 0.012" material="{accent}"/>
                  <site name="{prefix}_tcp" pos="0 0 0.05"/>
                </body>
              </body>
            </body>
          </body>
        </body>
      </body>
    </body>"""


def visual_xml() -> str:
    return f"""
<mujoco>
  <visual>
    <global offwidth="1920" offheight="1080"/>
    <quality shadowsize="4096" offsamples="8"/>
    <headlight ambient="0.28 0.29 0.32" diffuse="0.38 0.38 0.4" specular="0.1 0.1 0.1"/>
    <map znear="0.02" zfar="30"/>
  </visual>
  <asset>
    <texture name="sky" type="skybox" builtin="gradient" rgb1="0.1 0.13 0.18" rgb2="0.03 0.04 0.06" width="512" height="512"/>
    <texture name="grid" type="2d" builtin="checker" rgb1="0.12 0.14 0.18" rgb2="0.115 0.135 0.175" mark="edge" markrgb="0.22 0.27 0.34" width="512" height="512"/>
    <material name="floor" texture="grid" texrepeat="24 24" reflectance="0.12"/>
    <material name="shell" rgba="0.84 0.86 0.9 1" specular="0.6" shininess="0.6"/>
    <material name="steel" rgba="0.32 0.35 0.4 1" specular="0.6" shininess="0.5"/>
    <material name="base" rgba="0.18 0.2 0.24 1" specular="0.3"/>
    <material name="teal" rgba="0.18 0.83 0.75 1" emission="0.35"/>
    <material name="amber" rgba="0.98 0.75 0.14 1" emission="0.35"/>
  </asset>
  <worldbody>
    <light pos="-1 -2 3.5" dir="0.3 0.5 -1" diffuse="0.7 0.7 0.72" specular="0.3 0.3 0.3" castshadow="true"/>
    <light pos="2 2 2" dir="-0.5 -0.5 -0.6" diffuse="0.2 0.26 0.3" castshadow="false"/>
    <geom type="plane" size="6 6 0.1" material="floor"/>
    {arm_xml("mj", -0.46, -0.46, "amber")}
    {arm_xml("sp", 0.46, 0.46, "teal")}
  </worldbody>
</mujoco>"""


STEEL = np.array([0.32, 0.35, 0.4])
HOT = np.array([1.0, 0.36, 0.08])


def chart(dr, x0, y0, w, h, mj, sp, k, kmax, pmax):
    C.panel(dr, (x0, y0, x0 + w, y0 + h), a=0.82)
    C.text(dr, (x0 + 12, y0 + 8), "WINDING POWER FROM MOTION  (I²R minus gravity holding)", C.font(10), C.MUTED)
    gx, gy, gw, gh = x0 + 12, y0 + 26, w - 24, h - 36
    dr.line((gx, gy + gh, gx + gw, gy + gh), fill=C.alpha((38, 50, 68), 1), width=1)
    for run, col in ((mj, C.AMBER), (sp, C.TEAL)):
        pts = []
        for j in range(0, k + 1, 4):
            pts.append((gx + gw * j / kmax, gy + gh - gh * min(run[j]["p"].sum() / pmax, 1.0)))
        if len(pts) > 1:
            dr.line(pts, fill=C.alpha(col, 1), width=2, joint="curve")


def main() -> None:
    mj, sp = simulate(0.0), simulate(-11.0)
    dt = 0.001
    n = len(mj)
    pmax = max(max(r["p"].sum() for r in mj), max(r["p"].sum() for r in sp)) * 1.05
    sim_frames = int(round(n * dt / SLOW * C.FPS))
    e_mj, e_sp = mj[-1]["e"], sp[-1]["e"]

    m = mujoco.MjModel.from_xml_string(visual_xml())
    d = mujoco.MjData(m)
    r = mujoco.Renderer(m, C.H, C.W)
    cam = mujoco.MjvCamera()
    cam.lookat[:] = [0.0, 0.0, 0.18]
    cam.elevation = -11
    adr = {p: [m.joint(f"{p}j{i}").qposadr[0] for i in range(1, 7)] for p in ("mj", "sp")}
    hid = {p: [m.geom(f"{p}_h{i}").id for i in range(1, 7)] for p in ("mj", "sp")}
    tcp = {p: m.site(f"{p}_tcp").id for p in ("mj", "sp")}
    trail = {"mj": [], "sp": []}
    jmax = max(max(r["p"].max() for r in mj), max(r["p"].max() for r in sp))

    if FR.exists():
        shutil.rmtree(FR)
    FR.mkdir(parents=True)
    total = INTRO + sim_frames + OUTRO
    f_title, f_sub, f_lab, f_small, f_mono = C.font(22, "SemiBold"), C.font(13), C.font(12, "SemiBold"), C.font(11), C.mono(10)
    for fi in range(total):
        sf = min(max(fi - INTRO, 0), sim_frames)
        k = min(int(round(sf / C.FPS * SLOW / dt)), n - 1)
        prog = fi / total
        cam.azimuth = 122 + 26 * C.ease(prog)
        cam.distance = 2.75 - 0.15 * C.ease(prog)
        for p, run in (("mj", mj), ("sp", sp)):
            row = run[k]
            for a, q in zip(adr[p], row["q"]):
                d.qpos[a] = q
            for gi, pj in zip(hid[p], row["p"]):
                heat = min(1.0, (pj / jmax) ** 0.45)
                m.geom_rgba[gi, :3] = STEEL * (1 - heat) + HOT * heat
        mujoco.mj_forward(m, d)
        for p in ("mj", "sp"):
            if fi >= INTRO and sf < sim_frames:
                trail[p].append(d.site_xpos[tcp[p]].copy())
                trail[p] = trail[p][-40:]
        r.update_scene(d, cam)
        for p, col in (("mj", (0.98, 0.75, 0.14)), ("sp", (0.18, 0.83, 0.75))):
            pts = trail[p]
            for i in range(1, len(pts)):
                C.add_arrow(r.scene, pts[i - 1], pts[i] + 1e-6, (*col, 0.25 + 0.6 * i / len(pts)), width=0.005, kind="capsule")
        img = Image.fromarray(r.render())
        layer, dr = C.compose(img)

        ta = C.ease(fi / 10)
        C.text(dr, (24, 18), "Same move, less heat", f_title, a=ta)
        C.text(dr, (24, 48), "Identical arms, identical path and cycle time. Only the time profile differs.", f_sub, C.MUTED, ta)
        C.text(dr, (C.W - 24, 22), f"{SLOW:.1f}× speed   t = {k * dt:0.2f} s", f_mono, C.MUTED, 0.9, anchor="ra")

        for p, label, col in (("mj", "5th-order minimum jerk", C.AMBER), ("sp", "septic, η = −11", C.TEAL)):
            base = [-0.46, -0.46] if p == "mj" else [0.46, 0.46]
            pp = C.project(r.scene, [base[0], base[1], -0.05])
            if pp:
                w = dr.textlength(label, font=f_lab) + 22
                pp = (pp[0], min(pp[1] + 14, C.H - 134))
                C.panel(dr, (pp[0] - w / 2, pp[1] - 12, pp[0] + w / 2, pp[1] + 12), a=0.85, radius=12,
                        outline=C.alpha(col, 0.9))
                C.text(dr, (pp[0], pp[1]), label, f_lab, col, anchor="mm")

        # Power chart + cumulative heat
        chart(dr, 24, C.H - 112, 470, 92, mj, sp, k, n - 1, pmax)
        bx, by = 506, C.H - 112
        C.panel(dr, (bx, by, C.W - 24, by + 92), a=0.82)
        C.text(dr, (bx + 12, by + 8), "HEAT FROM MOTION, CUMULATIVE", C.font(10), C.MUTED)
        for i, (run, col, lab) in enumerate(((mj, C.AMBER, "min jerk"), (sp, C.TEAL, "septic"))):
            e = run[k]["e"]
            yy = by + 32 + i * 26
            C.text(dr, (bx + 12, yy - 2), lab, f_small, C.MUTED)
            C.bar(dr, bx + 70, yy, 120, 9, e / e_mj, col)
            C.text(dr, (C.W - 34, yy - 3), f"{e:5.0f} J", f_mono, C.TEXT, anchor="ra")

        if fi >= INTRO + sim_frames - 6:
            a = C.ease((fi - (INTRO + sim_frames - 6)) / 12)
            cx, cy = 24, 74
            C.panel(dr, (cx, cy, cx + 232, cy + 118), a=0.88 * a)
            C.text(dr, (cx + 14, cy + 10), f"−{100 * (e_mj - e_sp) / e_mj:.0f}% heat from motion", C.font(18, "SemiBold"), C.TEAL, a)
            for i, s in enumerate(["same endpoints, same 0.8 s per move",
                                   "η = −11 is the proved optimum for",
                                   "inertial loss; any servo can run it",
                                   "one polynomial, emitted to C and ST"]):
                C.text(dr, (cx + 14, cy + 40 + i * 18), s, f_small, C.TEXT, a)

        C.flatten(img, layer).save(FR / f"f{fi:04d}.png")

    size = C.encode_gif(FR, OUT)
    print(OUT, f"{size / 1e6:.2f} MB", total, "frames", f"E_mj={e_mj:.1f} E_sp={e_sp:.1f}")


if __name__ == "__main__":
    main()
