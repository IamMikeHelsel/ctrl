"""Exact enclosure of the newly found zero-jerk-FF endpoint-rate schedule."""

import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

from inventor_cancellation import outward, propagate


def enclose(reset_disturbance_clock=False):
    # e=(actual-reference), s=exp(-20t), and a constant coordinate.
    # The exponential coordinate is retained across every jerk/rate join.
    center, radius = [F(0), F(0), F(0), F(1), F(1)], F(0)
    w_bound = F(1, 2000)
    phases = [
        (F(1, 50), 10, 12),
        (F(1, 50), -10, 12),
        (F(1, 50), -10, 8),
        (F(1, 50), 10, 8),
        (F(197, 500), 0, 10),
    ]
    audits = []
    time = F(0)
    for duration, jerk, rate in phases:
        if reset_disturbance_clock and time:
            # Deliberate mutation: physical error states remain, but this changes w(t).
            center[3] = F(1)
        matrix = [
            [F(0), F(1), F(0), F(0), F(0)],
            [F(0), F(0), F(1), F(0), F(0)],
            [F(-8 * rate), F(-6 * rate), F(-3 * rate, 2), rate * w_bound, -jerk - rate * w_bound],
            [F(0), F(0), F(0), F(-20), F(0)],
            [F(0)] * 5,
        ]
        center, radius, audit = propagate(matrix, duration, center, radius)
        time += duration
        audit.update(
            {
                "jerk": jerk,
                "rate": rate,
                "end_time": time,
                "position_lower": outward(center[0] - radius, True),
                "position_upper": outward(center[0] + radius, False),
                "exponential_coordinate_lower": outward(center[3] - radius, True),
                "exponential_coordinate_upper": outward(center[3] + radius, False),
            }
        )
        audits.append(audit)
    assert time == F(237, 500)
    lower, upper = outward(center[0] - radius, True), outward(center[0] + radius, False)
    assert lower > F(1, 5000)
    assert upper - lower <= F(1, 10**17)
    result = {
        "contract": {
            "sigma": 1,
            "kappa": 0,
            "reference_jerks": [10, -10, -10, 10],
            "jerk_phase_duration": F(1, 50),
            "reference_final_position": F(1, 6250),
            "total_original_horizon": F(102, 25),
            "rate_schedule": "12 on[0,.04),8 on[.04,.08),10 on[.08,4.08]",
            "disturbance": "-(1/2000)*(1-exp(-20t))",
            "initial_error": [0, 0, 0],
            "reference_and_physical_state_resets": False,
        },
        "witness_time": time,
        "position_error_lower_m": lower,
        "position_error_upper_m": upper,
        "stages": audits,
        "evidence": "Exact Fraction Taylor enclosure and analytic infinite-tail majorant; not a Lean theorem or global maximum claim.",
    }
    result["deliberately_reset_disturbance_clock"] = reset_disturbance_clock
    return result


def main():
    source_directory = Path(
        "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/tracking-replans"
    )
    saved_comparison = json.loads((source_directory / "comparison-results.json").read_text())
    assert saved_comparison["profiles"]["short_high_jerk"] == {
        "J_m_s3_exact": "10",
        "h_s_exact": "1/50",
        "final_position_m_exact": "1/6250",
    }
    bound_rows = [
        r
        for r in saved_comparison["rows"]
        if r["profile"] == "short_high_jerk"
        and r["sigma"] == 1
        and r["method"] == "zero_jerk_ff"
        and r["disturbance_bound_m_s2"] == 0.0005
    ]
    assert len(bound_rows) == 4
    assert all(r["kappa_s_exact"] == "0" and r["total_horizon_s"] == 4.08 for r in bound_rows)
    result = enclose()
    result["source_binding"] = {
        "comparison_py_sha256": hashlib.sha256(
            (source_directory / "comparison.py").read_bytes()
        ).hexdigest(),
        "comparison_results_sha256": hashlib.sha256(
            (source_directory / "comparison-results.json").read_bytes()
        ).hexdigest(),
        "matching_existing_rows": len(bound_rows),
        "new_rate_schedule_was_not_one_of_saved_four": True,
    }
    mutation = enclose(reset_disturbance_clock=True)
    assert mutation["position_error_lower_m"] > result["position_error_upper_m"]
    result["clock_reset_negative_control"] = {
        "description": "Reset exponential coordinate to1 at phase joins: changes named original disturbance while preserving physical/error states. Still bounded in magnitude by W, so not a counterexample to a robust-W assumption.",
        "mutated_lower_m": mutation["position_error_lower_m"],
        "mutated_upper_m": mutation["position_error_upper_m"],
        "strictly_separated_from_original_enclosure": True,
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, default=str, indent=2) + "\n")
    print(
        "zeroFF at",
        result["witness_time"],
        "lower",
        result["position_error_lower_m"],
        "upper",
        result["position_error_upper_m"],
        "float",
        float(result["position_error_lower_m"]),
        "degrees",
        [a["degree"] for a in result["stages"]],
    )


if __name__ == "__main__":
    main()
