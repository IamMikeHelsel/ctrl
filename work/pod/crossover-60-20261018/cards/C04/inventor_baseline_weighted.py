"""Exact unchanged-gain refinement with weighted prefix and bounded pending duration."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
KMAX = F(2407079, 50250000)
PENDING_SLOPE = F(97066, 12500)  # 7.76528, actual C5 startup box.
PENDING_DURATION = F(1, 2000)
WEIGHTED_CAP = (F(19, 10) * F(9, 200) - F(3, 1700)) * F(4, 3)


def test(age):
    w = 2 * F(606, 25) * KMAX + F(103, 1000)
    coarse = w
    steps = []
    for i in range(1, 5):
        slope = max(F(2432, 25) * KMAX + 4 * w, F(2012, 25) * KMAX + 6 * w)
        pending_extra = max(F(0), PENDING_SLOPE - slope) * min(age, PENDING_DURATION)
        next_w = F(103, 1000) + slope * age + pending_extra
        steps.append(
            {
                "pass": i,
                "input": str(w),
                "holding_slope": str(slope),
                "pending_extra": str(pending_extra),
                "output": str(next_w),
                "margin_to_weighted_cap": str(WEIGHTED_CAP - next_w),
                "fits_weighted_cap": next_w < WEIGHTED_CAP,
            }
        )
        w = next_w
    return {"age": str(age), "coarse": str(coarse), "steps": steps}


def main():
    command_bound = F(606, 25) * KMAX + F(93, 1000)
    assert command_bound < 2
    # Physical-coordinate derivative coefficients independently explain the two
    # weighted slope norms: (-32,64,0) at8; (-16,16,48) at12.
    assert 32 * F(51, 50) + 64 * F(101, 100) == F(2432, 25)
    assert 16 * F(51, 50) + 16 * F(101, 100) + 48 == F(2012, 25)
    failing_age = F(3, 2000)
    affine_fixed_point = (
        F(103, 1000)
        + F(2432, 25) * KMAX * (failing_age - PENDING_DURATION)
        + PENDING_SLOPE * PENDING_DURATION
    ) / (1 - 4 * (failing_age - PENDING_DURATION))
    assert affine_fixed_point > WEIGHTED_CAP
    result = {
        "scope": "Unchanged gains8,6,.5 and unchanged center/weighted clearance. Prefix K<=Kmax is the source-bound PM premise; this script checks algebra, not its first-contact discharge.",
        "Kmax": str(KMAX),
        "measured_command_bound": str(command_bound),
        "pending_duration": str(PENDING_DURATION),
        "pending_slope": str(PENDING_SLOPE),
        "weighted_shrinking_cap": str(WEIGHTED_CAP),
        "cases": [test(F(7, 5000)), test(F(3, 2000))],
        "history_binding": "The pending contribution is bounded by the overlap of the actual sample-to-now interval with global[0,D], never reset at each dispatch. Holding time is still charged for all remaining age.",
        "one_point_five_ms_obstruction": {
            "affine_lower_map_fixed_point": str(affine_fixed_point),
            "exceeds_weighted_cap": True,
            "scope": "The exact refinement map dominates this affine map; starting from the larger coarse bound, no number of these passes can fall below this fixed point. This refutes this sufficient budget at1.5ms, not physical safety or stronger proofs.",
        },
    }
    assert result["cases"][0]["steps"][2]["fits_weighted_cap"]
    (HERE / "inventor_baseline_weighted.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
