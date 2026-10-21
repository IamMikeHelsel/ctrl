"""Independent CSV metrics and same-state force reconstruction, no producer imports."""

import csv
import hashlib
import json
from pathlib import Path

import mujoco
import numpy as np

HERE = Path(__file__).resolve().parent
SOURCE = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/franka-demo-08"
)
MODEL = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/.tools/mujoco-menagerie"
)
manifest = json.loads((SOURCE / "model-provenance.json").read_text())
for file, digest in manifest["files"].items():
    assert hashlib.sha256((MODEL / file).read_bytes()).hexdigest() == digest
summary = json.loads((SOURCE / "results/summary.json").read_text())
assert (
    hashlib.sha256((SOURCE / "run_smoke.py").read_bytes()).hexdigest()
    == summary["run_script_sha256"]
)
m = mujoco.MjModel.from_xml_path(str(MODEL / "franka_fr3/scene.xml"))
d = mujoco.MjData(m)
assert m.nu == m.nv == 7
assert np.array_equal(m.actuator_trnid[:, 0], np.arange(7))
assert np.array_equal(m.jnt_dofadr, np.arange(7))
assert np.array_equal(m.actuator_trntype, np.zeros(7))
assert np.array_equal(m.actuator_gear, np.array([[1, 0, 0, 0, 0, 0]] * 7))
limits = m.jnt_actfrcrange[:, 1]
site = mujoco.mj_name2id(m, mujoco.mjtObj.mjOBJ_SITE, "attachment_site")
runs = []
for file in sorted((SOURCE / "results").glob("*.csv")):
    m.opt.timestep = 0.0005 if file.name.endswith("500us.csv") else 0.001
    rows = list(csv.DictReader(file.open()))
    maxima = {
        "actuator_replay_error": 0.0,
        "bias_replay_error": 0.0,
        "site_replay_error": 0.0,
        "acceleration_replay_error": 0.0,
        "raw_vs_generalized_error": 0.0,
    }
    totalmax = np.zeros(7)
    rawmax = np.zeros(7)
    biasmax = np.zeros(7)
    tracking = []
    goal = []
    worst = None
    maxratio = -1
    for row in rows:

        def vals(prefix, row=row):
            return np.array([float(row[f"{prefix}_{j}"]) for j in range(1, 8)])

        d.qpos[:] = vals("q_rad")
        d.qvel[:] = vals("v_rad_s")
        d.ctrl[:] = vals("command_rad")
        bias = vals("bias_assist_Nm")
        d.qfrc_applied[:] = bias
        mujoco.mj_forward(m, d)
        raw = vals("actuator_Nm")
        maxima["actuator_replay_error"] = max(
            maxima["actuator_replay_error"], float(np.max(np.abs(d.actuator_force - raw)))
        )
        maxima["raw_vs_generalized_error"] = max(
            maxima["raw_vs_generalized_error"], float(np.max(np.abs(d.qfrc_actuator - raw)))
        )
        if "model_bias_compensation" in file.name:
            maxima["bias_replay_error"] = max(
                maxima["bias_replay_error"], float(np.max(np.abs(d.qfrc_bias - bias)))
            )
        maxima["acceleration_replay_error"] = max(
            maxima["acceleration_replay_error"], float(np.max(np.abs(d.qacc - vals("a_rad_s2"))))
        )

        def xyz(prefix, row=row):
            return np.array([float(row[f"{prefix}_{a}"]) for a in "xyz"])

        actual = xyz("actual_flange_m")
        maxima["site_replay_error"] = max(
            maxima["site_replay_error"], float(np.max(np.abs(d.site_xpos[site] - actual)))
        )
        tracking.append(float(np.linalg.norm(actual - xyz("reference_flange_m"))))
        goal.append(float(np.linalg.norm(actual - xyz("goal_flange_m"))))
        total = d.qfrc_actuator + bias
        totalmax = np.maximum(totalmax, np.abs(total))
        rawmax = np.maximum(rawmax, np.abs(raw))
        biasmax = np.maximum(biasmax, np.abs(bias))
        ratio = float(np.max(np.abs(total) / limits))
        if ratio > maxratio:
            maxratio = ratio
            j = int(np.argmax(np.abs(total) / limits))
            worst = {
                "time_s": float(row["time_s"]),
                "joint": j + 1,
                "actuator_Nm": float(d.qfrc_actuator[j]),
                "bias_Nm": float(bias[j]),
                "total_Nm": float(total[j]),
                "model_limit_Nm": float(limits[j]),
                "ratio": ratio,
            }
    tail = [e for row, e in zip(rows, goal, strict=True) if float(row["time_s"]) >= 1.8]
    runs.append(
        {
            "file": file.name,
            "rows": len(rows),
            "max_total_per_joint_Nm": totalmax.tolist(),
            "max_raw_per_joint_Nm": rawmax.tolist(),
            "max_bias_per_joint_Nm": biasmax.tolist(),
            "worst_limit_ratio": worst,
            "max_tracking_error_m": max(tracking),
            "final_window_error_m": max(tail),
            "final_band_pass": max(tail) <= 0.0002,
            "same_state_reconstruction": maxima,
        }
    )
result = {
    "source_script_hash_verified": True,
    "model_files_verified": len(manifest["files"]),
    "runtime": mujoco.__version__,
    "mapping": "Seven direct joint actuators, unit gears, matching joint/DOF/actuator order; limits at joint actuatorfrcrange. Compare actual qfrc_actuator before adding bias.",
    "runs": runs,
    "scope": "All saved rows reconstructed by mj_forward; binary64 simulation consistency and sampled measurements, not continuous-time bounds or hardware limits.",
}
(HERE / "critic_trace.json").write_text(json.dumps(result, indent=2) + "\n")
print(
    json.dumps(
        {
            "rows": sum(r["rows"] for r in runs),
            "worst": max(runs, key=lambda r: r["worst_limit_ratio"]["ratio"]),
            "max_same_state_errors": {
                k: max(r["same_state_reconstruction"][k] for r in runs) for k in maxima
            },
        },
        indent=2,
    )
)
