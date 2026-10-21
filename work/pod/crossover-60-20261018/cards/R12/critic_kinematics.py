"""Independent centered-difference check of selected-state Jacobian diagnostics."""

import csv
import json
from pathlib import Path

import mujoco
import numpy as np

HERE = Path(__file__).resolve().parent
SOURCE = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/franka-demo-08/results"
)
m = mujoco.MjModel.from_xml_path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/.tools/mujoco-menagerie/franka_fr3/scene.xml"
)
d = mujoco.MjData(m)
site = mujoco.mj_name2id(m, mujoco.mjtObj.mjOBJ_SITE, "attachment_site")


def point(q):
    d.qpos[:] = q
    mujoco.mj_forward(m, d)
    return d.site_xpos[site].copy()


checks = []
for r in json.loads((HERE / "pm_kinematics.json").read_text())["results"]:
    rows = list(csv.DictReader((SOURCE / r["csv"]).open()))
    row = next(x for x in rows if float(x["time_s"]) == r["peak_time_s"])
    qa = np.array([float(row[f"q_rad_{i}"]) for i in range(1, 8)])
    qr = np.array([float(row[f"command_rad_{i}"]) for i in range(1, 8)])
    J = np.zeros((3, 7))
    eps = 1e-6
    for j in range(7):
        e = np.eye(7)[j] * eps
        J[:, j] = (point(qr + e) - point(qr - e)) / (2 * eps)
    remainder = float(np.linalg.norm(point(qa) - point(qr) - J @ (qa - qr)) * 1000)
    assert abs(remainder - r["linearization_remainder_mm"]) < 1e-7
    assert abs(np.linalg.norm(J, 2) - r["reference_state_J_spectral_norm_m_per_rad"]) < 1e-8
    checks.append(
        {
            "file": r["csv"],
            "finite_difference_J_norm": float(np.linalg.norm(J, 2)),
            "remainder_mm": remainder,
        }
    )
(HERE / "critic_kinematics.json").write_text(
    json.dumps(
        {
            "checks": checks,
            "scope": "Selected-state finite-difference verification of local diagnostic only. Neither pointwise norm nor finite-difference accuracy certifies a uniform tube.",
        },
        indent=2,
    )
    + "\n"
)
print("All16 selected local Jacobian diagnostics independently checked by centered differences.")
