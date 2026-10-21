"""Exact negative control for an explicitly changed baseline-stage model.

No source artifact is modified; this is not a failure of its existing checker.
"""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def valid(x):
    w, d, q, leakage = x
    return (
        -2 <= w <= 2
        and F(1, 2) <= abs(d) <= 1
        and F(1, 5) <= leakage <= F(3, 10)
        and q == leakage * d
        and F(9, 10) <= w + d <= F(11, 10)
        and F(7, 5) <= w + d + F(1, 2) <= F(8, 5)
    )


def weighted(rows, weights):
    return [
        sum((weight * row[j] for row, weight in zip(rows, weights, strict=True)), F(0))
        for j in range(4)
    ]


def main():
    if not __debug__:
        raise RuntimeError("Exact checks require assertions; do not run with -O")
    positive = (F(3, 5), F(1, 2), F(3, 20), F(3, 10))
    negative = (F(7, 5), F(-1, 2), F(-3, 20), F(3, 10))
    assert valid(positive) and valid(negative)
    # Every row stores [a_w,a_d,a_q,b] for a.x<=b.
    positive_rows = [
        [F(1), F(1), F(0), F(11, 10)],
        [F(0), F(-3, 10), F(1), F(0)],
        [F(0), F(-1), F(0), F(-1, 2)],
    ]
    negative_rows = [
        [F(-1), F(-1), F(0), F(-9, 10)],
        [F(0), F(3, 10), F(-1), F(0)],
        [F(0), F(1), F(0), F(-1, 2)],
    ]
    weights = [F(1), F(1, 2), F(17, 20)]
    assert all(weight >= 0 for weight in weights)
    assert weighted(positive_rows, weights) == [F(1), F(0), F(1, 2), F(27, 40)]
    assert weighted(negative_rows, weights) == [F(-1), F(0), F(-1, 2), F(-53, 40)]
    predictions = [x[0] + x[2] / 2 for x in (positive, negative)]
    assert predictions == [F(27, 40), F(53, 40)]
    observation = [F(19, 20), F(21, 20)]
    assert predictions[0] < observation[0] < observation[1] < predictions[1]
    out = {
        "status": "exact rational negative control; changed baseline-stage model",
        "changes": [
            "Add prior 1/2<=abs(d)<=1, preserving original w bounds and leakage bounds.",
            "Use baseline and redundant trial; do not apply original separating observation.",
            "Preserve heldout row (1,0,1/2), replace observation interval by [19/20,21/20].",
        ],
        "branch_witnesses_w_d_q_lambda": [[str(v) for v in x] for x in (positive, negative)],
        "hull_overlap_witness": "1",
        "positive_prediction_upper": "27/40",
        "negative_prediction_lower": "53/40",
        "dual_weights_for_both_bounds": [str(v) for v in weights],
        "exact_compatibility": False,
        "hull_compatibility": True,
        "application": "branch-preservation checker regression; no novel attribution method",
    }
    (HERE / "domain_gap_exact_results.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
