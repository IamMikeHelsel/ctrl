"""Exact small negative controls and sampled-reference interface allowance."""

import csv
import hashlib
import json
from fractions import Fraction as F
from math import comb
from pathlib import Path


def four_box_step(t, h):
    if t <= 0:
        return F(0)
    if t >= 4 * h:
        return F(1)
    return sum((-1) ** k * comb(4, k) * max(t - k * h, 0) ** 4 for k in range(5)) / (24 * h**4)


def reference(t):
    return F(1, 25) * four_box_step(t - F(11, 50), F(1, 5)) - F(3, 50) * four_box_step(
        t - F(67, 100), F(1, 5)
    )


def main():
    source = Path(
        "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/"
        "2026-10-17/robot-motion/franka-demo-08"
    )
    protocol_path = source / "protocol.json"
    protocol = json.loads(protocol_path.read_text())
    assert F(str(protocol["h_s"])) == F(1, 5)
    assert protocol["command_period_ns"] == 1000000
    packets = protocol["cases"]["queued_reversal"]
    assert [p["execute_ns"] for p in packets] == [220000000, 670000000]
    assert [F(str(p["target_rad"])) for p in packets] == [F(1, 25), F(-1, 50)]
    csv_path = source / "results/queued_reversal__model_bias_compensation__500us.csv"
    with csv_path.open() as handle:
        csv_rows = list(csv.DictReader(handle))
    decimal_discrepancy = max(
        abs(reference(F(r["time_s"])) - F(r["ref_offset_rad"])) for r in csv_rows
    )
    assert decimal_discrepancy < F(1, 10**14)
    # Individual scalar systems x'=-x are stable. The declared toy interconnection
    # x'=-x+2y, y'=2x-y has positive eigenvalue1 on direction(1,1).
    bad_matrix = ((F(-1), F(2)), (F(2), F(-1)))
    vector = (F(1), F(1))
    image = tuple(sum(a * v for a, v in zip(row, vector, strict=True)) for row in bad_matrix)
    assert image == vector
    # A rational weighted row certificate for the separate good toy.
    good_matrix = ((F(-1), F(1, 4)), (F(1, 2), F(-1)))
    good_image = tuple(sum(a * v for a, v in zip(row, vector, strict=True)) for row in good_matrix)
    assert good_image == (F(-3, 4), F(-1, 2))
    assert all(v <= F(-1, 2) for v in good_image)

    # Four-box density max is2/3: piece on[0,1] is x^3/6; on[1,2]
    # (-3x^3+12x^2-12x+4)/6 has derivative zeros2/3,2; reflect about2.
    h, command_period = F(1, 5), F(1, 1000)
    kernel_peak = F(2, 3) / h
    positive_velocity_bound = F(1, 25) * kernel_peak
    negative_velocity_bound = F(3, 50) * kernel_peak
    assert positive_velocity_bound == F(2, 15)
    assert negative_velocity_bound == F(1, 5)
    # Positive and negative histories have nonnegative kernels, so their difference
    # lies between minus the negative bound and the positive bound, not their sum.
    held_interface_error_bound = command_period * max(
        positive_velocity_bound, negative_velocity_bound
    )
    assert held_interface_error_bound == F(1, 5000)
    t0, t1 = F(1069, 1000), F(1070, 1000)
    interior = t1 - F(1, 1000000)
    jump = reference(t1) - reference(t0)
    intersample_error = reference(interior) - reference(t0)
    assert F(0) < abs(intersample_error) < abs(jump) <= held_interface_error_bound
    # The staircase command is discontinuous at t1, so finite ordinary jerk of
    # the analytic reference cannot be assigned to that emitted command.
    assert jump != 0

    result = {
        "source_binding": {
            "protocol_sha256": hashlib.sha256(protocol_path.read_bytes()).hexdigest(),
            "csv_sha256": hashlib.sha256(csv_path.read_bytes()).hexdigest(),
            "sample_count": len(csv_rows),
            "maximum_exact_reference_to_decimal_saved_sample_discrepancy_rad": decimal_discrepancy,
            "discrepancy_float_for_display": float(decimal_discrepancy),
            "scope": "Saved sample comparison only, not a bound on arbitrary runtime floating evaluation.",
        },
        "toy_coupling_negative": {
            "matrix": bad_matrix,
            "positive_eigenvector": vector,
            "image": image,
            "scope": "Not an FR3 identified model; falsifies implication from isolated scalar stability alone.",
        },
        "toy_weighted_row_certificate": {
            "matrix": good_matrix,
            "positive_weights": vector,
            "row_image": good_image,
            "contraction_rate": F(1, 2),
        },
        "queued_reference_held_interface": {
            "h_s": h,
            "command_period_s": command_period,
            "positive_velocity_bound_rad_s": positive_velocity_bound,
            "negative_velocity_bound_rad_s": negative_velocity_bound,
            "uniform_joint_command_error_bound_rad": held_interface_error_bound,
            "sample_start_s": t0,
            "next_sample_s": t1,
            "jump_rad": jump,
            "interior_time_s": interior,
            "interior_error_rad": intersample_error,
        },
        "warning": "The input allowance is for the ideal four-box reference and its exact zero-order hold. CSV implementation rounding and physical tracking need separate bounds; no radian-to-meter conversion or FR3 closed-loop gain is certified here.",
    }
    text = json.dumps(result, default=str, indent=2)
    Path(__file__).with_suffix(".json").write_text(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
