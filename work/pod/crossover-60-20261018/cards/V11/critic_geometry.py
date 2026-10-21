"""Independent halfspace and information-algebra verification; exact rational arithmetic."""

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).parent
source = json.loads((HERE / "inventor_geometry.json").read_text())
H = [(F(1), F(0)), (F(0), F(1)), (F(1), F(1)), (F(1), F(2))]
z = [F(1), F(0), F(0), F(0)]
e = F(1, 100)


def vertices(inliers):
    constraints = [(F(1), F(0), F(1)), (F(-1), F(0), F(1)), (F(0), F(1), F(1)), (F(0), F(-1), F(1))]
    for i in inliers:
        a, b = H[i]
        constraints.extend([(a, b, z[i] + e), (-a, -b, -z[i] + e)])
    found = set()
    for (a, b, c), (d, f, g) in combinations(constraints, 2):
        det = a * f - b * d
        if det == 0:
            continue
        point = ((c * f - b * g) / det, (a * g - c * d) / det)
        if all(A * point[0] + B * point[1] <= C for A, B, C in constraints):
            found.add(point)
    return found


results = []
for case in source["cases"]:
    allpoints = set()
    actual_masks = set()
    for branch in case["branches"]:
        mask = tuple(branch["assumed_inliers"])
        own = vertices(mask)
        reported = set(tuple(map(F, p)) for p in branch["vertices"])
        assert own == reported
        if own:
            actual_masks.add(mask)
        allpoints |= own
    assert len(actual_masks) == case["feasible_branch_count"]
    for label, key in [
        ("all_data_information_candidate", "all_data_candidate"),
        ("certified_inlier_information_candidate", "certified_inlier_candidate"),
    ]:
        record = case[label]
        Y = [list(map(F, row)) for row in record["information"]]
        P = [list(map(F, row)) for row in record["covariance"]]
        mu = list(map(F, record["mean"]))
        for i in range(2):
            for j in range(2):
                assert sum(Y[i][k] * P[k][j] for k in range(2)) == int(i == j)
        if label.startswith("all_data"):
            weights = [F(10000)] + [F(1)] * (case["n"] - 1)
            selected = list(range(case["n"]))
        else:
            selected = case["certified_inlier_rows"]
            weights = [F(10000)] * case["n"]
        expected = [
            [
                F(int(i == j)) + sum(weights[k] * H[k][i] * H[k][j] for k in selected)
                for j in range(2)
            ]
            for i in range(2)
        ]
        assert Y == expected
        information_vector = [sum(weights[k] * H[k][i] * z[k] for k in selected) for i in range(2)]
        assert mu == [sum(P[i][j] * information_vector[j] for j in range(2)) for i in range(2)]
        radius = max(max(abs(p[i] - mu[i]) for i in range(2)) for p in allpoints)
        assert radius == F(case["joint_set_worst_error_bounds"][key])
    results.append(
        {
            "rows": case["n"],
            "nonempty_masks": [list(m) for m in sorted(actual_masks)],
            "distinct_vertices": len(allpoints),
        }
    )
# Sharp general pair for arbitrary bounded one-outlier worlds.
A = (F(0), F(0))
B = (6 * e, -4 * e)
obs = (F(0), -4 * e, e, -e)
for point in [A, B]:
    errors = [abs(a * point[0] + b * point[1] - v) for (a, b), v in zip(H, obs, strict=True)]
    assert sum(err > e for err in errors) == 1
assert max(abs(B[i] - A[i]) for i in range(2)) == 6 * e
# Threshold negative control: at epsilon1/4 a false row1-retaining branch survives.
point = (F(3, 4), F(-1, 4))
epsilon = F(1, 4)
assert all(abs(H[k][0] * point[0] + H[k][1] * point[1] - z[k]) <= epsilon for k in [0, 1, 3])
(HERE / "critic_geometry.json").write_text(
    json.dumps(
        {
            "reconstructed_branches": results,
            "sharp_general_diameter": str(6 * e),
            "threshold_false_branch": [str(v) for v in point],
            "scope": "Exact rational enumeration and inverse/mean checks, independent of producer vertices. Conditional on prior, common state, bounded inlier noise and at most one faulty original row. No camera-model or probabilistic claim.",
        },
        indent=2,
    )
    + "\n"
)
print(json.dumps(results, indent=2))
