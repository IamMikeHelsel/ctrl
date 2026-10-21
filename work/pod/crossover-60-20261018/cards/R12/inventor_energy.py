"""Read-only recorded generalized-bias work and command-semantics diagnostics."""

import csv
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

SOURCE = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/"
    "2026-10-17/robot-motion/franka-demo-08/results"
)


def trapezoid(times, samples):
    return sum(
        (t1 - t0) * (s0 + s1) / 2
        for t0, t1, s0, s1 in zip(times[:-1], times[1:], samples[:-1], samples[1:], strict=True)
    )


def norm(xs):
    return math.sqrt(sum(x * x for x in xs))


def replay(path):
    with path.open() as handle:
        original = list(csv.DictReader(handle))
    rows = [{key: float(value) for key, value in row.items()} for row in original]
    time = [r["time_s"] for r in rows]
    bias = [[r[f"bias_assist_Nm_{j}"] for j in range(1, 8)] for r in rows]
    velocity = [[r[f"v_rad_s_{j}"] for j in range(1, 8)] for r in rows]
    power_components = [
        [b * v for b, v in zip(bs, vs, strict=True)] for bs, vs in zip(bias, velocity, strict=True)
    ]
    signed_power = [sum(p) for p in power_components]
    joint_absolute_power = [sum(abs(p) for p in ps) for ps in power_components]
    squared_bias = [sum(b * b for b in bs) for bs in bias]
    command_steps = [
        abs(b["command_rad_1"] - a["command_rad_1"])
        for a, b in zip(rows[:-1], rows[1:], strict=True)
    ]
    tracking_error = [
        norm([r[f"actual_flange_m_{a}"] - r[f"reference_flange_m_{a}"] for a in "xyz"])
        for r in rows
    ]
    off_axis = [norm([r[f"q_rad_{j}"] - rows[0][f"q_rad_{j}"] for j in range(2, 8)]) for r in rows]
    joint1_error = [abs(r["q_rad_1"] - r["command_rad_1"]) for r in rows]
    peak_index = max(range(len(rows)), key=tracking_error.__getitem__)
    result = {
        "file": path.name,
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "rows": len(rows),
        "saved_dt_s": time[1] - time[0],
        "bias_signed_work_sampled_J": trapezoid(time, signed_power),
        "bias_absolute_net_power_integral_sampled_J": trapezoid(
            time, [abs(p) for p in signed_power]
        ),
        "bias_joint_absolute_work_sampled_J": trapezoid(time, joint_absolute_power),
        "bias_squared_torque_integral_sampled_Nm2s": trapezoid(time, squared_bias),
        "peak_bias_Nm": max(abs(b) for bs in bias for b in bs),
        "peak_bias_power_W": max(abs(p) for p in signed_power),
        "peak_tracking_error_m": tracking_error[peak_index],
        "peak_tracking_at_s": time[peak_index],
        "joint1_error_at_peak_rad": joint1_error[peak_index],
        "uncommanded_joint_displacement_at_peak_rad": off_axis[peak_index],
        "max_uncommanded_joint_displacement_rad": max(off_axis),
        "peak_joint1_error_rad": max(joint1_error),
        "max_command_jump_rad": max(command_steps),
        "command_total_variation_rad": sum(command_steps),
        "max_reported_continuous_reference_jerk_rad_s3": max(
            abs(r["ref_jerk_rad_s3"]) for r in rows
        ),
    }
    if path.name.startswith("hold__model_bias_compensation"):
        # Exact statements about the decimal CSV, not an integration-error certificate.
        assert all(Fraction(r[f"v_rad_s_{j}"]) == 0 for r in original for j in range(1, 8))
        assert all(Fraction(r[f"actuator_Nm_{j}"]) == 0 for r in original for j in range(1, 8))
        assert all(
            Fraction(r[f"bias_assist_Nm_{j}"]) == Fraction(original[0][f"bias_assist_Nm_{j}"])
            for r in original
            for j in range(1, 8)
        )
        assert result["bias_signed_work_sampled_J"] == 0
        assert result["peak_bias_Nm"] > 25
        exact_duty = sum(Fraction(original[0][f"bias_assist_Nm_{j}"]) ** 2 for j in range(1, 8)) * 2
        result["exact_constant_hold_squared_bias_integral_decimal_CSV"] = str(exact_duty)
    return result


def main():
    paths = sorted(SOURCE.glob("*.csv"))
    assert len(paths) == 16
    result = {
        "scope": "Sampled replay only. Bias is generalized force from qfrc_applied; actuator outputs are not summed without transmission validation. Work is trapezoidal mechanical work, not electrical energy, dissipation, or a continuous-time bound.",
        "runs": [replay(p) for p in paths],
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    for r in result["runs"]:
        print(
            r["file"],
            "work",
            round(r["bias_signed_work_sampled_J"], 9),
            "abs-joint-work",
            round(r["bias_joint_absolute_work_sampled_J"], 9),
            "duty",
            round(r["bias_squared_torque_integral_sampled_Nm2s"], 6),
            "error-mm",
            round(r["peak_tracking_error_m"] * 1000, 6),
            "off-axis-rad",
            round(r["max_uncommanded_joint_displacement_rad"], 9),
            "jump",
            r["max_command_jump_rad"],
        )


if __name__ == "__main__":
    main()
