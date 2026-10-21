"""Independent numpy quadrature and exact constant-hold checks."""

import csv
import json
from fractions import Fraction as F
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
SOURCE = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/franka-demo-08/results"
)
producer = json.loads((HERE / "inventor_energy.json").read_text())
checks = []
for record in producer["runs"]:
    rows = list(csv.DictReader((SOURCE / record["file"]).open()))
    t = np.array([float(r["time_s"]) for r in rows])
    b = np.array([[float(r[f"bias_assist_Nm_{j}"]) for j in range(1, 8)] for r in rows])
    v = np.array([[float(r[f"v_rad_s_{j}"]) for j in range(1, 8)] for r in rows])
    power = b * v
    vals = {
        "bias_signed_work_sampled_J": float(np.trapezoid(power.sum(axis=1), t)),
        "bias_absolute_net_power_integral_sampled_J": float(
            np.trapezoid(abs(power.sum(axis=1)), t)
        ),
        "bias_joint_absolute_work_sampled_J": float(np.trapezoid(abs(power).sum(axis=1), t)),
        "bias_squared_torque_integral_sampled_Nm2s": float(np.trapezoid((b * b).sum(axis=1), t)),
    }
    for name, value in vals.items():
        assert abs(record[name] - value) <= 1e-10 * max(1, abs(value))
    assert vals["bias_absolute_net_power_integral_sampled_J"] + 1e-14 >= abs(
        vals["bias_signed_work_sampled_J"]
    )
    assert (
        vals["bias_joint_absolute_work_sampled_J"] + 1e-14
        >= vals["bias_absolute_net_power_integral_sampled_J"]
    )
    if record["file"].startswith("hold__model_bias_compensation"):
        assert all(F(r[f"v_rad_s_{j}"]) == 0 for r in rows for j in range(1, 8))
        exact = 2 * sum(F(rows[0][f"bias_assist_Nm_{j}"]) ** 2 for j in range(1, 8))
        assert exact == F(record["exact_constant_hold_squared_bias_integral_decimal_CSV"])
        assert vals["bias_signed_work_sampled_J"] == 0 and exact > 2000
    checks.append({"file": record["file"], "independent_quadrature": vals})
(HERE / "critic_energy.json").write_text(
    json.dumps(
        {
            "checked_runs": checks,
            "scope": "Mechanical work and squared-torque duty only; neither electrical energy nor thermal safety. Original current/voltage/temperature are absent.",
        },
        indent=2,
    )
    + "\n"
)
print("Independent quadrature and exact constant-hold certificate pass all16 files.")
