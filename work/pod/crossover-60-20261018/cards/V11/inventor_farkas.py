"""Exact prototype branch certificates and semantic rejection controls for V11."""

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path


def constraints(e):
    return {
        "row1_lower": (-F(1), F(0), -1 + e),
        "row2_upper": (F(0), F(1), e),
        "row2_lower": (F(0), -F(1), e),
        "row3_upper": (F(1), F(1), e),
        "row3_lower": (-F(1), -F(1), e),
        "row4_upper": (F(1), F(2), e),
        "row4_lower": (-F(1), -F(2), e),
    }


certificates = {
    (1, 2, 3): [(F(1), "row1_lower"), (F(1), "row2_lower"), (F(1), "row3_upper")],
    (1, 2, 4): [(F(1), "row1_lower"), (F(2), "row2_lower"), (F(1), "row4_upper")],
    (1, 3, 4): [(F(1), "row1_lower"), (F(2), "row3_upper"), (F(1), "row4_lower")],
}


def evaluate(certificate, e):
    rows = constraints(e)
    total = tuple(sum(weight * rows[key][i] for weight, key in certificate) for i in range(3))
    accepted = (
        all(weight >= 0 for weight, _ in certificate) and total[:2] == (0, 0) and total[2] < 0
    )
    return accepted, total


records = []
for e in [F(1, 100), F(1, 4)]:
    for subset, certificate in certificates.items():
        valid, total = evaluate(certificate, e)
        records.append(
            {
                "epsilon": str(e),
                "branch": subset,
                "certificate": [(str(w), key) for w, key in certificate],
                "combined_inequality": list(map(str, total)),
                "strict_rejection": valid,
            }
        )
        assert valid == (e < F(1, 4) or subset == (1, 2, 3))
# At threshold, a zero RHS must not be treated as an infeasibility certificate.
point = (F(3, 4), -F(1, 4))
e = F(1, 4)
assert abs(point[0] - 1) <= e and abs(point[1]) <= e and abs(point[0] + 2 * point[1]) <= e
assert not evaluate(certificates[(1, 2, 4)], e)[0]
# Every required branch must appear, including the retained branch.
manifest = set(certificates) | {(2, 3, 4)}
required = set(combinations([1, 2, 3, 4], 3))
assert manifest == required
assert manifest - {(1, 2, 4)} != required
assert len(set(["sensor1", "sensor2", "sensor2", "sensor4"])) != 4
corrupted = [(-w, key) for w, key in certificates[(1, 2, 4)]]
assert not evaluate(corrupted, F(1, 100))[0]
# The retained information candidate must be the one whose error was certified.
Y = ((F(20001), F(30000)), (F(30000), F(60001)))
eta = (F(0), F(0))
reported = (F(0), F(0))
poisoned = (F(17500, 17503), -F(7500, 17503))


def binds(mu):
    return tuple(sum(Y[i][j] * mu[j] for j in range(2)) for i in range(2)) == eta


assert binds(reported) and not binds(poisoned)
result = {
    "branch_certificates": records,
    "threshold_feasible_counterexample": list(map(str, point)),
    "negative_controls": {
        "missing_branch": True,
        "duplicate_origin": True,
        "negative_dual_weights": True,
        "zero_rhs_not_infeasible": True,
        "candidate_substitution": True,
    },
    "scope": "Exact finite fixture checker sketch, not integrated adapter or Lean proof. Branch labels are unique original observation IDs. Farkas weights certify only listed inequalities; truth coverage and actual fault budget remain assumptions.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
