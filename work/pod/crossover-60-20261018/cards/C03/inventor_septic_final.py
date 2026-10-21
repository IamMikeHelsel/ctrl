"""Independent replay of repaired scoped gate; preserves failed audit artifacts."""

import ast
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
raw = (HERE / "pm_septic.py").read_bytes()
node = next(
    n for n in ast.parse(raw.decode()).body if isinstance(n, ast.FunctionDef) and n.name == "gate"
)
env = {"F": F}
exec(compile(ast.Module(body=[node], type_ignores=[]), "<final-septic-gate>", "exec"), env)
gate = env["gate"]
saved = json.loads((HERE / "pm_septic.json").read_text())["cases"]
for row in saved:
    assert gate(row["request"]) == row["result"]
base = saved[0]["request"]
probes = [
    ("negative_latency", {"latency": "-1/200"}, "UNKNOWN"),
    ("narrow_corridor", {"corridor": ["0", "1/48000"]}, "REJECT"),
    ("continuous_snap", {"regularity": "continuous_snap"}, "UNKNOWN"),
    ("undeclared_continuity_field", {"continuous_snap_required": True}, "UNKNOWN"),
    ("incoming_jerk", {"initial": ["0", "0", "0", "1"]}, "UNKNOWN"),
    ("outside_initial_corridor", {"corridor": ["1/100000", "1"]}, "REJECT"),
    ("late_commit", {"latency": "1/50"}, "UNKNOWN"),
    ("zero_distance_rest", {"distance": "0", "corridor": ["0", "0"]}, "ADMIT_REFERENCE"),
]
results = []
for name, change, expected in probes:
    request = {**base, **change}
    result = gate(request)
    assert result["decision"] == expected
    results.append({"name": name, "request": request, "result": result})
assert gate({k: v for k, v in base.items() if k != "regularity"})["decision"] == "UNKNOWN"
assert gate(base)["bounds"] == {
    "velocity": "7/7680",
    "acceleration": "7/64",
    "jerk": "35/16",
    "snap": "350",
}
out = {
    "producer_sha256": hashlib.sha256(raw).hexdigest(),
    "saved_cases_reproduced": len(saved),
    "independent_probes": results,
    "missing_regularity_rejected_as_unknown": True,
    "failed_prototype_evidence_preserved": "inventor_septic.json",
    "scope": "Reference-only typed-rational request prototype; not a total malformed-input parser or physical trajectory certificate.",
}
(HERE / "inventor_septic_final.json").write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            "sha256": out["producer_sha256"],
            "saved_cases": len(saved),
            "independent_probes": len(results),
            "status": "passed",
        }
    )
)
