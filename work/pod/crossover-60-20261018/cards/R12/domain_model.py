"""Read-only reconstruction of pinned saved FR3 states; no rollout or hardware."""

import csv
import hashlib
import json
from pathlib import Path

import mujoco
import numpy as np

SRC = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/franka-demo-08"
)
CACHE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/.tools/mujoco-menagerie"
)
OUT = Path(__file__).with_suffix(".json")
manifest = json.loads((SRC / "model-provenance.json").read_text())
assert all(
    hashlib.sha256((CACHE / p).read_bytes()).hexdigest() == h for p, h in manifest["files"].items()
)
m = mujoco.MjModel.from_xml_path(str(CACHE / "franka_fr3/scene.xml"))
d = mujoco.MjData(m)
limits = np.asarray(m.jnt_actfrcrange)
res = {
    "mujoco": mujoco.__version__,
    "model_hashes_checked": len(manifest["files"]),
    "nq": m.nq,
    "nv": m.nv,
    "nu": m.nu,
    "gear": m.actuator_gear.tolist(),
    "transmission_type": m.actuator_trntype.tolist(),
    "joint_force_limits": limits.tolist(),
    "actuator_force_limited": m.actuator_forcelimited.tolist(),
    "files": [],
    "snapshots": [],
}
for f in sorted((SRC / "results").glob("*.csv")):
    with f.open() as h:
        rows = list(csv.DictReader(h))

    def cols(prefix, rows=rows):
        return np.array([[float(r[f"{prefix}_{i + 1}"]) for i in range(7)] for r in rows])

    raw = cols("actuator_Nm")
    bias = cols("bias_assist_Nm")
    clipped = np.clip(raw, limits[:, 0], limits[:, 1])
    total = clipped + bias
    q = cols("q_rad")
    v = cols("v_rad_s")
    command = cols("command_rad")
    errors = np.array(
        [
            np.linalg.norm(
                [
                    float(r[f"actual_flange_m_{a}"]) - float(r[f"reference_flange_m_{a}"])
                    for a in "xyz"
                ]
            )
            for r in rows
        ]
    )
    loc = np.unravel_index(np.argmax(np.abs(total) / limits[:, 1]), total.shape)
    res["files"].append(
        {
            "file": f.name,
            "rows": len(rows),
            "max_raw_clamp_difference": float(np.max(np.abs(raw - clipped))),
            "max_total_to_xml_limit_ratio": float((np.abs(total) / limits[:, 1])[loc]),
            "witness_time": float(rows[loc[0]]["time_s"]),
            "witness_joint": int(loc[1] + 1),
            "raw": float(raw[loc]),
            "clamped": float(clipped[loc]),
            "bias": float(bias[loc]),
            "total": float(total[loc]),
            "peak_tracking_mm": float(errors.max() * 1000),
        }
    )
    if f.name == "queued_reversal__model_bias_compensation__500us.csv":
        for k in sorted({0, int(np.argmax(errors)), int(loc[0]), len(rows) - 1}):
            mujoco.mj_resetData(m, d)
            m.opt.timestep = 0.0005
            d.qpos[:] = q[k]
            d.qvel[:] = v[k]
            d.ctrl[:] = command[k]
            d.qfrc_applied[:] = bias[k]
            mujoco.mj_forward(m, d)
            mass = np.zeros((m.nv, m.nv))
            mujoco.mj_fullM(m, d, mass)
            jac = np.zeros((3, m.nv))
            rot = np.zeros((3, m.nv))
            site = mujoco.mj_name2id(m, mujoco.mjtObj.mjOBJ_SITE, "attachment_site")
            mujoco.mj_jacSite(m, d, jac, rot, site)
            rhs = (
                d.qfrc_actuator + d.qfrc_applied + d.qfrc_passive + d.qfrc_constraint - d.qfrc_bias
            )
            kp = np.asarray(m.actuator_gainprm[:, 0])
            kv = -np.asarray(m.actuator_biasprm[:, 2])
            qd_v = np.zeros(7)
            qd_a = np.zeros(7)
            qd_v[0] = float(rows[k]["ref_velocity_rad_s"])
            qd_a[0] = float(rows[k]["ref_acceleration_rad_s2"])
            e = q[k] - command[k]
            diagnostic_lag = -kv / kp * qd_v
            error_lhs = mass @ (d.qacc - qd_a) + kv * (v[k] - qd_v) + kp * e
            error_rhs = (
                (bias[k] - d.qfrc_bias)
                + d.qfrc_passive
                + d.qfrc_constraint
                - mass @ qd_a
                - kv * qd_v
            )
            res["snapshots"].append(
                {
                    "time": float(rows[k]["time_s"]),
                    "max_csv_actuator_vs_runtime": float(np.max(np.abs(raw[k] - d.actuator_force))),
                    "max_clipped_vs_qfrc_actuator": float(
                        np.max(np.abs(clipped[k] - d.qfrc_actuator))
                    ),
                    "bias_reconstruction_error": float(np.max(np.abs(bias[k] - d.qfrc_bias))),
                    "equation_residual": float(np.max(np.abs(mass @ d.qacc - rhs))),
                    "servo_formula_residual": float(
                        np.max(np.abs(raw[k] - (kp * (command[k] - q[k]) - kv * v[k])))
                    ),
                    "coupled_error_equation_residual": float(np.max(np.abs(error_lhs - error_rhs))),
                    "kp": kp.tolist(),
                    "kv": kv.tolist(),
                    "reference_velocity": qd_v.tolist(),
                    "quasistatic_velocity_lag": diagnostic_lag.tolist(),
                    "actual_error": e.tolist(),
                    "missing_velocity_ff_norm2": float(np.linalg.norm(kv * qd_v)),
                    "missing_acceleration_ff_norm2": float(np.linalg.norm(mass @ qd_a)),
                    "M": mass.tolist(),
                    "eig_M": np.linalg.eigvalsh(mass).tolist(),
                    "offdiagonal_frobenius": float(np.linalg.norm(mass - np.diag(np.diag(mass)))),
                    "jacobian_norm2": float(np.linalg.norm(jac, 2)),
                    "joint_error_norm2": float(np.linalg.norm(q[k] - command[k])),
                    "tracking_mm": float(errors[k] * 1000),
                    "passive": d.qfrc_passive.tolist(),
                    "constraint": d.qfrc_constraint.tolist(),
                }
            )
OUT.write_text(json.dumps(res, indent=2) + "\n")
print(
    json.dumps(
        {k: res[k] for k in ["mujoco", "model_hashes_checked", "files", "snapshots"]}, indent=2
    )
)
