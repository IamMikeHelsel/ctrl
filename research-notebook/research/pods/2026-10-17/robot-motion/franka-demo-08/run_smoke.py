"""Franka geometry/dynamics integration smoke. This program cannot contact a robot.

The inherited scalar Lean theorem does NOT cover this model or this Python code.
All control history is evaluated on integer simulated robot-clock ticks.
"""
from pathlib import Path
import argparse
import csv
import hashlib
import json
import platform
import sys

import mujoco
import numpy as np

HERE = Path(__file__).resolve().parent


def box_step(z, derivative=0):
    """Four unit boxes integrated once, and its first three derivatives."""
    if z <= 0:
        return 0.0
    if z >= 4:
        return 1.0 if derivative == 0 else 0.0
    # Symmetry avoids cancellation in the tail. This is numerical evaluation.
    if z > 2:
        v = box_step(4 - z, derivative)
        return (1 - v) if derivative == 0 else ((-1) ** (derivative + 1)) * v
    power = 4 - derivative
    denom = [24, 6, 2, 1][derivative]
    return sum(c * max(z - i, 0.0) ** power for i, c in enumerate((1, -4, 6, -4, 1))) / denom


class ReferenceHistory:
    def __init__(self, h):
        self.h = h
        self.events = []
        self.epoch = 0
        self.final_target = 0.0

    def receive(self, packet, now_ns):
        if not (packet["issue_ns"] <= packet["arrival_ns"] <= now_ns <= packet["execute_ns"]):
            raise ValueError("Packet issue/arrival/execution violates causality")
        if packet["epoch"] <= self.epoch:
            raise ValueError("Duplicate or stale authoritative goal epoch")
        if self.events and packet["execute_ns"] < self.events[-1][0]:
            raise ValueError("New execution precedes an existing commitment")
        self.events.append((packet["execute_ns"], packet["target_rad"] - self.final_target))
        self.final_target = packet["target_rad"]
        self.epoch = packet["epoch"]

    def at(self, now_ns):
        return np.array([sum(delta * box_step((now_ns - t) / 1e9 / self.h, d) / self.h**d
                             for t, delta in self.events) for d in range(4)])


def run_one(model_root, config, name, mode, dt, output):
    model = mujoco.MjModel.from_xml_path(str(model_root / "franka_fr3/scene.xml"))
    model.opt.timestep = dt
    data, reference_data, goal_data = (mujoco.MjData(model) for _ in range(3))
    for d in (data, reference_data, goal_data):
        mujoco.mj_resetDataKeyframe(model, d, 0)
        mujoco.mj_forward(model, d)
    home = data.qpos.copy()
    site = mujoco.mj_name2id(model, mujoco.mjtObj.mjOBJ_SITE, "attachment_site")
    joint = config["joint_index"]
    history = ReferenceHistory(config["h_s"])
    packets = config["cases"][name]
    received = 0
    command_period = config["command_period_ns"]
    step_ns = int(round(dt * 1e9))
    if command_period % step_ns:
        raise ValueError("Integration step must divide command period exactly")
    final_ns = int(round(config["duration_s"] * 1e9))
    samples, max_contacts = [], 0
    ref = np.zeros(4)
    command = home.copy()
    current_goal = 0.0
    goal_xyz = data.site_xpos[site].copy()
    ref_xyz = goal_xyz.copy()
    applied_bias = np.zeros(model.nv)
    for now_ns in range(0, final_ns + step_ns, step_ns):
        # States are logged at their actual clock, before advancing integration.
        if now_ns % command_period == 0:
            while received < len(packets) and packets[received]["arrival_ns"] <= now_ns:
                history.receive(packets[received], now_ns)
                received += 1
            ref = history.at(now_ns)
            command = home.copy()
            command[joint] += ref[0]
            data.ctrl[:] = command
            # Truth is used ONLY for task scoring, never by the executor.
            issued = [p for p in packets if p["issue_ns"] <= now_ns]
            current_goal = issued[-1]["target_rad"] if issued else 0.0
            reference_data.qpos[:] = command
            goal_data.qpos[:] = home
            goal_data.qpos[joint] += current_goal
            mujoco.mj_forward(model, reference_data)
            mujoco.mj_forward(model, goal_data)
            ref_xyz = reference_data.site_xpos[site].copy()
            goal_xyz = goal_data.site_xpos[site].copy()
        # Both configurations keep the original model gains, friction and limits.
        # Bias assist includes modeled gravity and Coriolis, not friction.
        mujoco.mj_forward(model, data)
        applied_bias = data.qfrc_bias.copy() if mode == "model_bias_compensation" else np.zeros(model.nv)
        data.qfrc_applied[:] = applied_bias
        mujoco.mj_forward(model, data)
        max_contacts = max(max_contacts, data.ncon)
        if not np.isfinite(np.concatenate([data.qpos, data.qvel, data.qacc])).all():
            raise RuntimeError("Nonfinite physical state")
        if now_ns % command_period == 0:
            samples.append(np.concatenate([[now_ns / 1e9, current_goal, *ref],
                data.qpos.copy(), data.qvel.copy(), data.qacc.copy(), command.copy(),
                data.actuator_force.copy(), applied_bias.copy(), data.site_xpos[site].copy(), ref_xyz, goal_xyz]))
        if now_ns < final_ns:
            mujoco.mj_step(model, data)
    arr = np.asarray(samples)
    cols = ["time_s", "goal_joint1_offset_rad", "ref_offset_rad", "ref_velocity_rad_s", "ref_acceleration_rad_s2", "ref_jerk_rad_s3"]
    for prefix in ("q_rad", "v_rad_s", "a_rad_s2", "command_rad", "actuator_Nm", "bias_assist_Nm"):
        cols.extend(f"{prefix}_{i+1}" for i in range(7))
    for prefix in ("actual_flange_m", "reference_flange_m", "goal_flange_m"):
        cols.extend(f"{prefix}_{axis}" for axis in "xyz")
    tag = f"{name}__{mode}__{round(dt*1e6)}us"
    with (output / f"{tag}.csv").open("w") as f:
        writer = csv.writer(f); writer.writerow(cols); writer.writerows(arr)
    actual, reference, goal = arr[:, -9:-6], arr[:, -6:-3], arr[:, -3:]
    tracking_error = np.linalg.norm(actual-reference, axis=1)
    task_error = np.linalg.norm(actual-goal, axis=1)
    tail = arr[:, 0] >= config["final_deadline_s"]
    warnings = {mujoco.mjtWarning(i).name: int(x.number) for i, x in enumerate(data.warning) if x.number}
    # Finite differences are diagnostics, not all-time jerk bounds.
    sampled_jerk = np.diff(arr[:, 20:27], axis=0) / (command_period/1e9)
    metrics = {"case": name, "servo": mode, "integration_dt_s": dt, "rows": len(arr),
        "max_tracking_flange_error_m": float(tracking_error.max()),
        "max_goal_flange_error_m": float(task_error.max()),
        "final_window_max_goal_flange_error_m": float(task_error[tail].max()),
        "final_window_position_pass": bool(np.all(task_error[tail] <= config["position_tolerance_m"])),
        "sampled_joint_jerk_max_rad_s3": float(abs(sampled_jerk).max()),
        "peak_joint_speed_rad_s": float(abs(arr[:, 13:20]).max()),
        "max_contacts": max_contacts, "warnings": warnings,
        "smoke_pass": not warnings,
        "commands_sha256": hashlib.sha256(arr[:, 27:34].astype("<f8").tobytes()).hexdigest()}
    return metrics, arr


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--model-root", type=Path, required=True)
    p.add_argument("--output", type=Path, default=HERE / "results")
    a = p.parse_args()
    a.output.mkdir(parents=True, exist_ok=True)
    cfg = json.loads((HERE / "protocol.json").read_text())
    manifest = json.loads((HERE / "model-provenance.json").read_text())
    for path, digest in manifest["files"].items():
        if hashlib.sha256((a.model_root / path).read_bytes()).hexdigest() != digest:
            raise RuntimeError(f"Model differs from pinned source: {path}")
    results, arrays = [], {}
    for case in cfg["cases"]:
        for mode in cfg["servo_configurations"]:
            for dt in cfg["integration_steps_s"]:
                metric, arr = run_one(a.model_root.resolve(), cfg, case, mode, dt, a.output)
                results.append(metric); arrays[(case, mode, dt)] = arr
    refinement = []
    for case in cfg["cases"]:
        for mode in cfg["servo_configurations"]:
            coarse, fine = [arrays[(case, mode, dt)] for dt in cfg["integration_steps_s"]]
            same_commands = np.array_equal(coarse[:, 27:34], fine[:, 27:34])
            if not same_commands:
                raise RuntimeError("Changed commands across integration resolutions")
            refinement.append({"case": case, "servo": mode, "same_commands": same_commands,
                "max_joint_position_difference_rad": float(abs(coarse[:, 6:13]-fine[:, 6:13]).max()),
                "max_flange_difference_m": float(np.linalg.norm(coarse[:, -9:-6]-fine[:, -9:-6],axis=1).max())})
    summary = {"scope": cfg["status"], "platform": platform.platform(), "python": sys.version,
        "mujoco": mujoco.__version__, "protocol_sha256": hashlib.sha256((HERE/"protocol.json").read_bytes()).hexdigest(),
        "run_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "model_commit": manifest["commit"], "runs": results, "refinement": refinement}
    (a.output / "summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    for r in results:
        print(r["case"], r["servo"], r["integration_dt_s"], "smoke",r["smoke_pass"],"final-window-mm",round(1000*r["final_window_max_goal_flange_error_m"],4))
    if not all(r["smoke_pass"] for r in results):
        raise SystemExit("MuJoCo warning: inspect summary")


if __name__ == "__main__":
    main()
