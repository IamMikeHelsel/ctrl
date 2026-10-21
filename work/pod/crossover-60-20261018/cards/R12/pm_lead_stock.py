"""Dependency negative: velocity lead cannot replace ideal gravity/bias assist."""

import importlib.util
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
spec = importlib.util.spec_from_file_location("source_smoke_negative", SOURCE / "run_smoke.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
namespace = dict(module.__dict__)
source = (HERE / "pm_lead_run_one.py.txt").read_text()
exec(compile(source, str(HERE / "pm_lead_run_one.py.txt"), "exec"), namespace)
output = HERE / "pm_lead_runs" / "stock_500us_gain0.1"
output.mkdir(parents=True, exist_ok=True)
metric, arr = namespace["run_one"](
    MODEL,
    json.loads((SOURCE / "protocol.json").read_text()),
    "queued_reversal",
    "stock_position",
    0.0005,
    output,
    0.1,
)
assert np.max(abs(arr[:, 41:48])) == 0
result = {
    "negative": "Sameleadwithoutidealbiasassist; comparisonistooriginalsourcefinalwindowband, notanassumedtransientband.",
    "metrics": metric,
    "bias_assist_zero": True,
    "alltimeclaim": False,
}
(HERE / "pm_lead_stock.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
