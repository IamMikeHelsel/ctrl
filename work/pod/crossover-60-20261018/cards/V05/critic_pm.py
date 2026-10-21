"""Independently consume PM fixture data and verify exact certificate premises."""

import json
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent
data = json.loads((HERE / "pm_fixture.json").read_text())
P = [tuple(map(F, x)) for x in data["sources"]]
Q = [tuple(map(F, x)) for x in data["targets"]]


def distance2(x, y):
    return sum((a - b) ** 2 for a, b in zip(x, y, strict=True))


def cost(source, target, t, epsilon=F(1), reflection=False):
    return sum(
        min(
            F(1),
            distance2((x[0] + t[0], x[1] + t[1], (-x[2] if reflection else x[2]) + t[2]), y)
            / epsilon**2,
        )
        for x, y in zip(source, target, strict=True)
    )


for record in data["cross_certificate"]:
    i, j = record["i"], record["j"]
    assert F(record["source_sq"]) == distance2(P[i], P[j]) < F(49, 16)
    assert record["target_x_difference"] == Q[j][0] - Q[i][0] >= 9
assert {(r["i"], r["j"]) for r in data["cross_certificate"]} == set(product(range(3), range(3, 6)))
for rec in data["candidate_poses"]:
    assert (
        cost(P, Q, tuple(map(F, rec["translation"])), reflection=rec["reflection"])
        == F(rec["tls"])
        == 3
    )
assert cost(P, Q, (F(5), F(0), F(0)), F(15, 2)) == F(8, 3)
P7 = P + [(F(0), F(0), F(2))]
Q7 = Q + [(F(0), F(0), F(2))]
for i, j in product((0, 1, 2, 6), (3, 4, 5)):
    assert distance2(P7[i], P7[j]) < F(49, 16) and Q7[j][0] - Q7[i][0] >= 9
for group in ((0, 1, 2, 6), (3, 4, 5)):
    for i, j in combinations(group, 2):
        assert distance2(P7[i], P7[j]) == distance2(Q7[i], Q7[j]) >= 1
assert cost(P7, Q7, (0, 0, 0)) == 3
assert cost(P7, Q7, (10, 0, 0)) == 4
assert cost(P7, Q7, (0, 0, 0), reflection=True) == 4
# 0,e1,e2,2e3 fixes the complete affine map; determinant of edge matrix is2.
assert P7[0] == (0, 0, 0) and P7[1] == (1, 0, 0) and P7[2] == (0, 1, 0) and P7[6] == (0, 0, 2)
changed = Q7[:-1] + [(F(10), F(0), F(2))]
assert cost(P7, changed, (0, 0, 0)) == 4 and cost(P7, changed, (10, 0, 0)) == 3
result = {
    "six_pair_all_cross_rows_checked": 9,
    "seven_pair_all_cross_rows_checked": 12,
    "seven_A_affine_determinant": "2",
    "threshold_mutation_midpoint": "8/3",
    "target_mutation_changes_preferred_fit": True,
    "classification_scope": "Handproof continuousTLSlower3 for all s>0 and O3; equality forces all4 A exact in7pairfixture, hence affineidentity. Not kernel uniqueness and not true-world identification without acquisition assumptions.",
}
(HERE / "critic_pm.json").write_text(json.dumps(result, indent=2) + "\n")
print(result)
