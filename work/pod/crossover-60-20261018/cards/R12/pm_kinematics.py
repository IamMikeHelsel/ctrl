"""Independent recorded-state task-space decomposition; numerical, not a tube proof."""

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
for name, digest in manifest["files"].items():
    assert hashlib.sha256((MODEL / name).read_bytes()).hexdigest() == digest
model = mujoco.MjModel.from_xml_path(str(MODEL / "franka_fr3/scene.xml"))
data = mujoco.MjData(model)
site = mujoco.mj_name2id(model, mujoco.mjtObj.mjOBJ_SITE, "attachment_site")


def flange(q):
    data.qpos[:] = q
    mujoco.mj_forward(model, data)
    return data.site_xpos[site].copy()


results = []
for path in sorted((SOURCE / "results").glob("*.csv")):
    a = np.genfromtxt(path, delimiter=",", names=True)

    def columns(names, data=a):
        return np.column_stack([data[n] for n in names])

    q = columns([f"q_rad_{i}" for i in range(1, 8)])
    ref = columns([f"command_rad_{i}" for i in range(1, 8)])
    actual = columns([f"actual_flange_m_{c}" for c in "xyz"])
    target = columns([f"reference_flange_m_{c}" for c in "xyz"])
    errors = np.linalg.norm(actual - target, axis=1)
    k = int(np.argmax(errors))
    qa = q[k]
    qr = ref[k]
    fa, fr = flange(qa), flange(qr)
    assert np.max(abs(fa - actual[k])) < 1e-13 and np.max(abs(fr - target[k])) < 1e-13
    only1 = qr.copy()
    only1[0] = qa[0]
    others = qa.copy()
    others[0] = qr[0]
    f1, fo = flange(only1), flange(others)
    flange(qr)
    jp, jr = np.zeros((3, model.nv)), np.zeros((3, model.nv))
    mujoco.mj_jacSite(model, data, jp, jr, site)
    linear = jp @ (qa - qr)
    results.append(
        {
            "csv": path.name,
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "peak_time_s": float(a["time_s"][k]),
            "tracking_mm": float(errors[k] * 1000),
            "joint_errors_rad": (qa - qr).tolist(),
            "only_joint1_error_mm": float(np.linalg.norm(f1 - fr) * 1000),
            "only_other_joints_error_mm": float(np.linalg.norm(fo - fr) * 1000),
            "linearized_vector_mm": (1000 * linear).tolist(),
            "linearization_remainder_mm": float(np.linalg.norm(fa - fr - linear) * 1000),
            "joint_error_norm_rad": float(np.linalg.norm(qa - qr)),
            "reference_state_J_spectral_norm_m_per_rad": float(np.linalg.norm(jp, 2)),
            "sample_joint_accel_peak_rad_s2": float(
                np.max(abs(columns([f"a_rad_s2_{i}" for i in range(1, 8)])))
            ),
            "analytic_reference_accel_peak_rad_s2": float(
                np.max(abs(a["ref_acceleration_rad_s2"]))
            ),
            "scope": "Selected actual peak state; coordinate replacement is a kinematic diagnostic, not a separately simulated plant. Jacobian value atonepoint is not a uniform Lipschitz bound.",
        }
    )
(HERE / "pm_kinematics.json").write_text(
    json.dumps(
        {
            "runtime": mujoco.__version__,
            "model_commit": manifest["commit"],
            "model_hashes_checked": len(manifest["files"]),
            "results": results,
        },
        indent=2,
    )
    + "\n"
)
for x in results:
    if "queued_reversal" in x["csv"] and "500us" in x["csv"]:
        print(json.dumps(x, indent=2))
