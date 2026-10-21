"""Fresh stock-no-bias dynamics loop; reuses only original ReferenceHistory, not producer run_one."""

import importlib.util
import json
from pathlib import Path

import mujoco
import numpy as np

HERE = Path(__file__).resolve().parent
SRC = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/franka-demo-08"
)
spec = importlib.util.spec_from_file_location("critic_reference_source", SRC / "run_smoke.py")
source = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)
config = json.loads((SRC / "protocol.json").read_text())
m = mujoco.MjModel.from_xml_path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/.tools/mujoco-menagerie/franka_fr3/scene.xml"
)
m.opt.timestep = 0.0005
d = mujoco.MjData(m)
refdata = mujoco.MjData(m)
goaldata = mujoco.MjData(m)
for obj in (d, refdata, goaldata):
    mujoco.mj_resetDataKeyframe(m, obj, 0)
    mujoco.mj_forward(m, obj)
home = d.qpos.copy()
site = mujoco.mj_name2id(m, mujoco.mjtObj.mjOBJ_SITE, "attachment_site")
history = source.ReferenceHistory(config["h_s"])
packets = config["cases"]["queued_reversal"]
received = 0
samples = []
for step in range(4001):
    ns = step * 500000
    if step % 2 == 0:
        while received < len(packets) and packets[received]["arrival_ns"] <= ns:
            history.receive(packets[received], ns)
            received += 1
        ref = history.at(ns)
        command = home.copy()
        command[0] += ref[0] + 0.1 * ref[1]
        d.ctrl[:] = command
        issued = [p for p in packets if p["issue_ns"] <= ns]
        goal = issued[-1]["target_rad"] if issued else 0
        refdata.qpos[:] = home
        refdata.qpos[0] += ref[0]
        goaldata.qpos[:] = home
        goaldata.qpos[0] += goal
        mujoco.mj_forward(m, refdata)
        mujoco.mj_forward(m, goaldata)
    mujoco.mj_forward(m, d)
    bias = np.zeros(m.nv)
    d.qfrc_applied[:] = bias
    mujoco.mj_forward(m, d)
    if step % 2 == 0:
        samples.append(
            np.r_[
                ns / 1e9,
                goal,
                ref,
                d.qpos,
                d.qvel,
                d.qacc,
                command,
                d.actuator_force,
                bias,
                d.site_xpos[site],
                refdata.site_xpos[site],
                goaldata.site_xpos[site],
            ]
        )
    if step < 4000:
        mujoco.mj_step(m, d)
a = np.array(samples)
producer = HERE / "pm_lead_runs/stock_500us_gain0.1/queued_reversal__stock_position__500us.csv"
b = np.genfromtxt(producer, delimiter=",", skip_header=1)
maxdiff = float(abs(a - b).max())
assert maxdiff < 1e-12
tracking = np.linalg.norm(a[:, -9:-6] - a[:, -6:-3], axis=1)
task = np.linalg.norm(a[:, -9:-6] - a[:, -3:], axis=1)
metrics = {
    "peak_original_reference_tracking_mm": float(tracking.max() * 1000),
    "final_task_window_mm": float(task[a[:, 0] >= 1.8].max() * 1000),
    "peak_goal_error_mm": float(task.max() * 1000),
    "peak_joint_speed_rad_s": float(abs(a[:, 13:20]).max()),
    "sampled_joint_jerk_rad_s3": float(abs(np.diff(a[:, 20:27], axis=0) / 0.001).max()),
    "max_total_force_limit_ratio": float(
        (abs(a[:, 34:41] + a[:, 41:48]) / np.array([87, 87, 87, 87, 12, 12, 12])).max()
    ),
}
assert np.all(a[:, 41:48] == 0)
assert metrics["final_task_window_mm"] > 0.2
result = {
    "source_final_window_position_pass": False,
    "ideal_bias_disabled": True,
    "fresh_loop_vs_producer_max_absolute": maxdiff,
    "metrics": metrics,
    "shared_code": "Original ReferenceHistory only, disclosed; dynamics loop independently written, no producer run_one or string transformations used.",
    "scope": "Fixed2s, .5ms integration, saved1ms samples; original reference/goal scoring retained. No new controller theorem or physical validation.",
}
(HERE / "critic_lead_stock.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
