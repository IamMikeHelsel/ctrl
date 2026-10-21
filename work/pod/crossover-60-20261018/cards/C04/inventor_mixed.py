"""Pure rational mixed-history and weighted-face acceptance for a new gain candidate."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
R = F(2221, 40000)
P, Q, H = F(16, 3), F(6), F(1, 2)
M = P / 1000 + Q / 100 + H / 20
D = F(1, 100)
AGE = F(3, 200)
WEIGHTS = [F(51, 50), F(101, 100), F(1)]
TARGET, DRIFT = F(9, 200), F(3, 1700)


def main():
    pending = []
    for r, v, a, disturbance in product(
        (F(8), F(12)),
        (F(-1533, 50000), F(1533, 50000)),
        (F(-33, 25), F(33, 25)),
        (-D, D),
    ):
        slope = -P * v - Q * a - H * r * (F(-121, 100) + disturbance - a)
        pending.append((abs(slope), [r, v, a, disturbance]))
    pending_max, pending_witness = max(pending)
    command_coefficients = [F(32, 3), F(-8), F(-8)]
    command_gain = sum(abs(x) for x in command_coefficients)
    command_bound = command_gain * R + M
    assert command_bound < 2

    def mixed_slope(w):
        return max(pending_max, 128 * R + 4 * w, F(352, 3) * R + 6 * w)

    coarse = 2 * command_gain * R + M + D
    passes = []
    w = coarse
    for number in range(1, 5):
        slope = mixed_slope(w)
        next_w = M + D + AGE * slope
        passes.append(
            {
                "pass": number,
                "input_mismatch": str(w),
                "mixed_slope": str(slope),
                "output_mismatch": str(next_w),
            }
        )
        w = next_w
    residual = F(passes[2]["output_mismatch"])
    assert residual < F(23, 100)
    weighted_limits = []
    weighted_face_rows = []
    for r in (F(8), F(12)):
        matrix = [
            [F(-4), F(4), F(0)],
            [F(0), F(-4), F(4)],
            [4 - r / 3, -12 + 3 * r / 2, 8 - 3 * r / 2],
        ]
        third_row = matrix[2][2] * WEIGHTS[2] + sum(abs(matrix[2][j]) * WEIGHTS[j] for j in (0, 1))
        weighted_limits.append((-third_row * TARGET - DRIFT) * 16 / r)
        for i, row in enumerate(matrix):
            other = [j for j in range(3) if j != i]
            for signs in product((-1, 1), repeat=2):
                z = [F(0)] * 3
                z[i] = WEIGHTS[i] * TARGET
                for j, sign in zip(other, signs, strict=True):
                    z[j] = sign * WEIGHTS[j] * TARGET
                derivative = sum(a * b for a, b in zip(row, z, strict=True))
                if i == 2:
                    derivative += r * residual / 16
                excess = derivative + WEIGHTS[i] * DRIFT
                weighted_face_rows.append(excess)
                assert excess <= 0
                coefficient = row[i] * WEIGHTS[i] + sum(abs(row[j]) * WEIGHTS[j] for j in other)
                assert coefficient < 0  # The same bound improves for K >= TARGET.
    assert residual < min(weighted_limits)
    baseline_pending = max(
        abs(-8 * v - 6 * a - r * (F(-121, 100) + disturbance - a) / 2)
        for r, v, a, disturbance in product(
            (F(8), F(12)),
            (F(-1533, 50000), F(1533, 50000)),
            (F(-33, 25), F(33, 25)),
            (-D, D),
        )
    )
    baseline_age = F(11, 10000)
    baseline_w = 48 * R + F(103, 1000)
    baseline_passes = []
    for _ in range(2):
        baseline_slope = max(baseline_pending, 96 * R + 4 * baseline_w, 80 * R + 6 * baseline_w)
        baseline_w = F(103, 1000) + baseline_age * baseline_slope
        baseline_passes.append({"slope": str(baseline_slope), "residual": str(baseline_w)})
    baseline_limits = []
    for r in (F(8), F(12)):
        row = [4 - r / 2, -12 + 3 * r / 2, 8 - 3 * r / 2]
        coefficient = abs(row[0]) * WEIGHTS[0] + abs(row[1]) * WEIGHTS[1] + row[2]
        baseline_limits.append((-coefficient * TARGET - DRIFT) * 16 / r)
    assert baseline_w < min(baseline_limits) and baseline_w < 8 * R / 3
    # First two transformed rows are gain-independent. Source startup geometry,
    # center and pending actual command are untouched by this calculation.
    result = {
        "scope": "New feedback gains, same center policy, weights, radius/target, drift, sensor box, pending command/startup bounds. Exact conditional prefix budgets; not a constructed execution or kernel safety theorem.",
        "gains": [str(P), str(Q), str(H)],
        "sensor_cost": str(M),
        "age": str(AGE),
        "radius": str(R),
        "pending_slope_max": str(pending_max),
        "startup_source": "constructive-hold-07/inputs/ClearanceAdmission.lean: startup_acceleration and startup_velocity, C5 bounds33/25 and1533/50000; older C3 bounds are not reused.",
        "pending_attaining_vertex": [str(x) for x in pending_witness],
        "measured_command_bound": str(command_bound),
        "clip_margin": str(2 - command_bound),
        "coarse_non_age_mismatch": str(coarse),
        "refinement_passes": passes,
        "selected_pass": 3,
        "derived_residual": str(residual),
        "derived_residual_float": float(residual),
        "uniform_cube_mismatch_limit": str(16 * R / 3),
        "weighted_drift_limits_at_rates_8_12": [str(x) for x in weighted_limits],
        "weighted_drift_limit": str(min(weighted_limits)),
        "residual_margin_to_weighted_limit": str(min(weighted_limits) - residual),
        "weighted_face_vertices_checked": len(weighted_face_rows),
        "weighted_face_max_excess": str(max(weighted_face_rows)),
        "uniform_cube_residual_margin": str(16 * R / 3 - residual),
        "unchanged_gain_baseline": {
            "gains": ["8", "6", "1/2"],
            "age": str(baseline_age),
            "pending_slope_max": str(baseline_pending),
            "coarse_mismatch": str(48 * R + F(103, 1000)),
            "two_refinement_passes": baseline_passes,
            "weighted_drift_limit": str(min(baseline_limits)),
            "weighted_drift_margin": str(min(baseline_limits) - baseline_w),
            "same_clearance_tube": True,
            "scope": "Exact conditional two-pass algebra, not a new compiled or constructed execution theorem.",
        },
        "proof_obligations": [
            "Rebuild actual command/mismatch and one-sided derivative lemmas for these gains.",
            "Generalize age_bound contract and all stamps, including first retained reading, to15ms.",
            "Use three finite prefix refinements and an inflated-box first-contact argument; do not assume mismatch invariant.",
            "Reuse unchanged startup geometry and center only after binding to actual source contract.",
            "Construct larger-age held flows and show clock/history compatibility before claiming operational safety.",
        ],
        "variation_reservoir_negative_control": {
            "scope": "Abstract bookkeeping counterexample, not a demonstrated original-plant trajectory.",
            "feedback_slope": "8",
            "reading_stamp": "0",
            "dispatch": "1/2000",
            "evaluation_time": "1/800",
            "available_variation_budget": "1/125",
            "incorrect_dispatch_reset_variation": str(F(8) * (F(1, 800) - F(1, 2000))),
            "correct_stamp_to_now_variation": str(F(8) * F(1, 800)),
            "false_reset_passes": F(8) * (F(1, 800) - F(1, 2000)) <= F(1, 125),
            "correct_full_history_fails": F(8) * F(1, 800) > F(1, 125),
            "repair": "Variation budget begins at the actual retained reading stamp; dispatch of an old reading cannot replenish it.",
        },
    }
    (HERE / "inventor_mixed.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
