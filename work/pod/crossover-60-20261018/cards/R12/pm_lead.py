"""Isolated causal reference-velocity lead experiment; original task score retained."""

import hashlib
import importlib.util
import inspect
import json
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
SOURCE = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/franka-demo-08"
)
MODEL = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/.tools/mujoco-menagerie"
)
spec = importlib.util.spec_from_file_location("source_smoke", SOURCE / "run_smoke.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
source = inspect.getsource(module.run_one)
assert source.count("command[joint] += ref[0]") == 1
assert source.count("reference_data.qpos[:] = command") == 1
source = source.replace(
    "def run_one(model_root, config, name, mode, dt, output):",
    "def run_one(model_root, config, name, mode, dt, output, lead_gain):",
)
source = source.replace("command[joint] += ref[0]", "command[joint] += ref[0] + lead_gain * ref[1]")
source = source.replace(
    "reference_data.qpos[:] = command",
    "reference_data.qpos[:] = home\n            reference_data.qpos[joint] += ref[0]",
)
(HERE / "pm_lead_run_one.py.txt").write_text(source)
namespace = dict(module.__dict__)
exec(compile(source, str(HERE / "pm_lead_run_one.py.txt"), "exec"), namespace)
config = json.loads((SOURCE / "protocol.json").read_text())
limits = np.array([87, 87, 87, 87, 12, 12, 12])
rows = []
for dt in [0.001, 0.0005]:
    for gain in [0, 0.1]:
        output = HERE / "pm_lead_runs" / f"{round(dt * 1e6)}us_gain{gain}"
        output.mkdir(parents=True, exist_ok=True)
        metric, arr = namespace["run_one"](
            MODEL, config, "queued_reversal", "model_bias_compensation", dt, output, gain
        )
        raw = arr[:, 34:41]
        bias = arr[:, 41:48]
        total = np.clip(raw, -limits, limits) + bias
        if gain == 0:
            original = np.genfromtxt(
                SOURCE
                / "results"
                / f"queued_reversal__model_bias_compensation__{round(dt * 1e6)}us.csv",
                delimiter=",",
                skip_header=1,
            )
            replay_error = float(np.max(abs(arr - original)))
            assert replay_error < 1e-12, replay_error
        else:
            replay_error = None
        rows.append(
            {
                "integration_dt_s": dt,
                "lead_gain_s": gain,
                "metrics": metric,
                "original_replay_max_abs": replay_error,
                "max_raw_actuator_limit_ratio": float(np.max(abs(raw) / limits)),
                "max_total_force_limit_ratio": float(np.max(abs(total) / limits)),
                "max_command_displacement_from_original_ref_rad": float(
                    np.max(abs(arr[:, 27] - arr[:, 2]))
                ),
                "scope": "Numerical2s replay. Only joint1 reference-velocity lead changed; original task and reference scoring, all gains, bias assist and joint force limits retained. No uniform tube or hardware claim.",
            }
        )
result = {
    "source_sha256": hashlib.sha256((SOURCE / "run_smoke.py").read_bytes()).hexdigest(),
    "transformation": "u1=qd1+0.1*qd_dot1 at1kHz; othercommandsunchanged. Reference flange scoring uses originalqd, notledcommand.",
    "results": rows,
}
(HERE / "pm_lead.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
