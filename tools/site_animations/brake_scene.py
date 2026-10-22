"""Scene + physics for the braking-shield animation."""
from __future__ import annotations

import numpy as np
import mujoco

from ctrl.robotics import (CentroidalQuadParams, safe_decel_max, directional_cbf,
                           lorentz_cbf_safety_filter, quad_contact_forces)

P = CentroidalQuadParams(m=40.0, g=9.81, h_g=0.45, w_x=0.25, w_y=0.18, mu=0.60)
X_LIMIT = 1.20                     # CoM keep-out (as in run_quadruped_zmp_cbf_benchmark)

EDGE_X = X_LIMIT + 0.25 + 0.012   # dock edge just past the front wheels at the limit
DROP = 0.7

PHYS = f"""
<mujoco>
  <option timestep="0.002" gravity="0 0 -9.81" integrator="RK4"/>
  <worldbody>
    <geom type="box" pos="{EDGE_X - 3} 0 -0.35" size="3 3 0.35" contype="0" conaffinity="1"/>
    <geom type="plane" pos="0 0 -{DROP}" size="10 10 0.1" contype="0" conaffinity="3" friction="0.8"/>
    <body name="trunk" pos="0 0 0.45">
      <freejoint/>
      <inertial pos="0 0 0" mass="40.0" diaginertia="1.2 2.4 2.8"/>
      <geom type="box" size="0.25 0.18 0.08" contype="1" conaffinity="1" mass="0"/>
      <geom type="sphere" pos="0.25 0.2 -0.36" size="0.09" contype="2" conaffinity="0" mass="0"/>
      <geom type="sphere" pos="0.25 -0.2 -0.36" size="0.09" contype="2" conaffinity="0" mass="0"/>
      <geom type="sphere" pos="-0.25 0.2 -0.36" size="0.09" contype="2" conaffinity="0" mass="0"/>
      <geom type="sphere" pos="-0.25 -0.2 -0.36" size="0.09" contype="2" conaffinity="0" mass="0"/>
    </body>
  </worldbody>
</mujoco>"""


def simulate(shield: bool, duration: float = 1.8):
    """Replicates the benchmark tick loop; returns per-step telemetry."""
    m = mujoco.MjModel.from_xml_string(PHYS)
    d = mujoco.MjData(m)
    a_brake = 0.92 * safe_decel_max(P.g, P.mu, P.w_x, P.h_g)
    d.qpos[0:3] = [0.0, 0.0, P.h_g]
    d.qpos[3:7] = [1, 0, 0, 0]
    d.qvel[0], d.qvel[1] = 3.0, 0.25
    mujoco.mj_forward(m, d)
    r_limit, n_hat, a_cbf, alpha = (X_LIMIT, 0.0, P.h_g), (1.0, 0.0, 0.0), (-1.0, 0.0, 0.0), 3.5
    out = []
    for k in range(int(round(duration / m.opt.timestep))):
        r = tuple(float(v) for v in d.qpos[0:3])
        v = tuple(float(x) for x in d.qvel[0:3])
        h = directional_cbf(r_limit, r, v, n_hat, a_brake)
        u_nom = (1.2, -1.5 * v[1], P.g)
        if shield:
            pi_b = (-a_brake if v[0] > 0.02 else 0.0, -2.0 * v[1], P.g)
            b_req = min(a_brake * (1.0 - alpha * h / max(v[0], 0.1)), a_brake) if v[0] > 0.02 else -10.0
            lam, u = lorentz_cbf_safety_filter(a_cbf, b_req, u_nom, pi_b)
        else:
            lam, u = 0.0, u_nom
        forces = quad_contact_forces(P, u[0], u[1])
        rot = d.xmat[1].reshape(3, 3)
        com = d.xpos[1].copy()
        net_f, net_t = np.zeros(3), np.zeros(3)
        support = {}
        for (ex, ey), f in forces.items():
            arm_w = rot @ np.array([ex * P.w_x, ey * P.w_y, -P.h_g])
            on = (com + arm_w)[0] < EDGE_X and com[2] > 0.3
            support[(ex, ey)] = on
            if on:
                fa = np.array(f)
                net_f += fa
                net_t += np.cross(arm_w, fa)
        d.xfrc_applied[1, 0:3] = net_f
        d.xfrc_applied[1, 3:6] = net_t
        contact = not all(support.values())
        out.append(dict(t=k * m.opt.timestep, qpos=d.qpos.copy(), v=v, h=h, lam=lam, ax=u[0],
                        forces={c: (np.array(f) if support[c] else None) for c, f in forces.items()}, contact=contact,
                        xmat=d.xmat[1].copy(), com=d.xpos[1].copy()))
        mujoco.mj_step(m, d)
    return out


def lane_body(name: str, y: float, accent: str) -> str:
    wheels = ""
    for i, (ex, ey) in enumerate([(1, 1), (1, -1), (-1, 1), (-1, -1)]):
        wx, wy = ex * 0.25, ey * 0.20
        wheels += f"""
      <geom type="capsule" fromto="{wx} {ey*0.13} -0.06 {wx} {wy} -0.33" size="0.018" material="strut"/>
      <body name="{name}_w{i}" pos="{wx} {wy} -0.36">
        <joint name="{name}_j{i}" type="hinge" axis="0 1 0"/>
        <geom type="cylinder" size="0.09 0.032" euler="90 0 0" material="tire"/>
        <geom type="cylinder" size="0.05 0.036" euler="90 0 0" material="hub_{name}"/>
        <geom type="box" size="0.072 0.004 0.012" pos="0 {ey*0.038} 0" material="spoke"/>
      </body>"""
    return f"""
    <body name="{name}" mocap="true" pos="0 {y} 0.45">
      <geom type="box" size="0.25 0.16 0.075" material="shell"/>
      <geom type="capsule" fromto="-0.25 0.16 0 0.25 0.16 0" size="0.075" material="shell"/>
      <geom type="capsule" fromto="-0.25 -0.16 0 0.25 -0.16 0" size="0.075" material="shell"/>
      <geom type="box" size="0.252 0.235 0.012" pos="0 0 0.02" material="{accent}"/>
      <geom type="box" size="0.18 0.12 0.02" pos="-0.02 0 0.085" material="deck"/>
      <geom type="cylinder" size="0.022 0.11" pos="0.14 0 0.19" material="strut"/>
      <geom type="box" size="0.05 0.08 0.035" pos="0.16 0 0.31" material="shell"/>
      <geom type="box" size="0.006 0.06 0.018" pos="0.212 0 0.31" material="{accent}"/>{wheels}
    </body>"""


def visual_xml() -> str:
    return f"""
<mujoco>
  <visual>
    <global offwidth="1920" offheight="1080"/>
    <quality shadowsize="4096" offsamples="8"/>
    <headlight ambient="0.3 0.31 0.34" diffuse="0.4 0.4 0.42" specular="0.1 0.1 0.1"/>
    <rgba haze="0.04 0.06 0.09 1"/>
    <map znear="0.05" zfar="40" haze="0.6"/>
  </visual>
  <asset>
    <texture name="sky" type="skybox" builtin="gradient" rgb1="0.1 0.13 0.18" rgb2="0.03 0.04 0.06" width="512" height="512"/>
    <texture name="grid" type="2d" builtin="checker" rgb1="0.11 0.13 0.17" rgb2="0.1 0.12 0.16" mark="edge" markrgb="0.22 0.27 0.34" width="512" height="512"/>
    <material name="floor" texture="grid" texrepeat="32 32" reflectance="0.1"/>
    <material name="shell" rgba="0.82 0.84 0.88 1" specular="0.6" shininess="0.6"/>
    <material name="deck" rgba="0.16 0.18 0.22 1" specular="0.3"/>
    <material name="strut" rgba="0.3 0.33 0.38 1" specular="0.5"/>
    <material name="tire" rgba="0.09 0.1 0.12 1" specular="0.2"/>
    <material name="spoke" rgba="0.75 0.77 0.8 1"/>
    <material name="teal" rgba="0.18 0.83 0.75 1" emission="0.35"/>
    <material name="rose" rgba="0.98 0.44 0.52 1" emission="0.35"/>
    <material name="hub_safe" rgba="0.18 0.83 0.75 1" emission="0.2"/>
    <material name="hub_raw" rgba="0.98 0.44 0.52 1" emission="0.2"/>
    <material name="dock" rgba="0.25 0.27 0.32 1" specular="0.2"/>
    <texture name="grid2" type="2d" builtin="checker" rgb1="0.13 0.15 0.19" rgb2="0.125 0.145 0.185" mark="edge" markrgb="0.24 0.28 0.35" width="512" height="512"/>
    <material name="lowfloor" texture="grid2" texrepeat="40 40" reflectance="0.05"/>
    <material name="limit" rgba="0.18 0.83 0.75 0.7" emission="0.5"/>
    <material name="hazard" rgba="0.98 0.75 0.14 1" emission="0.25"/>
  </asset>
  <worldbody>
    <light pos="-1.5 -2.5 4" dir="0.4 0.5 -1" diffuse="0.75 0.75 0.78" specular="0.3 0.3 0.3" castshadow="true"/>
    <light pos="3 2 2.5" dir="-0.6 -0.4 -0.6" diffuse="0.22 0.3 0.34" castshadow="false"/>
    <light pos="3.2 -2.5 2.2" dir="0 0.5 -1" diffuse="0.45 0.47 0.52" castshadow="true"/>
    <geom type="plane" pos="0 0 -{DROP}" size="12 12 0.1" material="lowfloor"/>
    <geom type="box" pos="{EDGE_X - 4} 0 -{DROP/2}" size="4 8 {DROP/2}" material="dock"/>
    <geom type="box" pos="{EDGE_X - 4} 0 0.0005" size="4 8 0.0005" material="floor"/>
    <geom type="box" pos="{EDGE_X - 0.02} 0 0.0012" size="0.02 8 0.0012" material="hazard"/>
    <geom type="box" pos="{EDGE_X + 0.0015} 0 -0.03" size="0.0015 8 0.03" material="hazard"/>
    <geom type="box" pos="{X_LIMIT + 0.25} 0 0.0016" size="0.003 8 0.0016" material="limit"/>
    {lane_body("safe", -0.85, "teal")}
    {lane_body("raw", 0.85, "rose")}
  </worldbody>
</mujoco>"""
