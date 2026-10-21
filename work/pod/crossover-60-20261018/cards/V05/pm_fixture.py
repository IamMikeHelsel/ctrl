"""Exact competing-registration certificate, independent of any TEASER run."""

import json
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

P = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1)]
Q = [p if i < 3 else (p[0] + 10, p[1], p[2]) for i, p in enumerate(P)]


def sq(a, b):
    return sum((F(x) - F(y)) ** 2 for x, y in zip(a, b, strict=True))


def objective(points, targets, translation, epsilon=F(1), reflection=False):
    residuals = [
        sq(
            (
                p[0] + translation[0],
                p[1] + translation[1],
                (-p[2] if reflection else p[2]) + translation[2],
            ),
            q,
        )
        for p, q in zip(points, targets, strict=True)
    ]
    return sum(min(r / (epsilon**2), F(1)) for r in residuals), residuals


cross = []
for i, j in product(range(3), range(3, 6)):
    row = {
        "i": i,
        "j": j,
        "source_sq": str(sq(P[i], P[j])),
        "target_x_difference": Q[j][0] - Q[i][0],
    }
    assert F(row["source_sq"]) < F(49, 16) and row["target_x_difference"] >= 9
    cross.append(row)
within = []
for group in (range(3), range(3, 6)):
    for i, j in combinations(group, 2):
        assert sq(P[i], P[j]) == sq(Q[i], Q[j]) >= 1
        within.append(
            {"i": i, "j": j, "source_sq": str(sq(P[i], P[j])), "target_sq": str(sq(Q[i], Q[j]))}
        )
poses = []
for reflection, t in [
    (False, (0, 0, 0)),
    (False, (10, 0, 0)),
    (True, (0, 0, 0)),
    (True, (10, 0, 2)),
]:
    value, residuals = objective(P, Q, t, reflection=reflection)
    assert value == 3
    poses.append(
        {
            "reflection": reflection,
            "determinant": -1 if reflection else 1,
            "translation": t,
            "tls": str(value),
            "residual_squared": list(map(str, residuals)),
        }
    )
# Noise-threshold mutation: old two-pose certificate cannot be reused at epsilon7.5.
mid, residuals = objective(P, Q, (5, 0, 0), F(15, 2))
assert mid == F(8, 3) < 3
# An added independent correspondence fixes an affine basis for the winning group.
P7 = P + [(0, 0, 2)]
Q7 = Q + [(0, 0, 2)]
a, _ = objective(P7, Q7, (0, 0, 0))
b, _ = objective(P7, Q7, (10, 0, 0))
mirror, _ = objective(P7, Q7, (0, 0, 0), reflection=True)
assert (a, b, mirror) == (3, 4, 4)
for i, j in product([0, 1, 2, 6], [3, 4, 5]):
    assert sq(P7[i], P7[j]) < F(49, 16) and Q7[j][0] - Q7[i][0] >= 9
for group in ([0, 1, 2, 6], [3, 4, 5]):
    for i, j in combinations(group, 2):
        assert sq(P7[i], P7[j]) == sq(Q7[i], Q7[j]) >= 1
result = {
    "sources": P,
    "targets": Q,
    "model": "Fixed labeled correspondences, s>0,R inSO3,t free, TLS sum min(||q-(sRp+t)||^2,1). No actual TEASER execution.",
    "cross_certificate": cross,
    "within_certificate": within,
    "scale_cases": {
        "s_le4": "source distance<7/4 gives scaled distance<7; target distance>=9. No two residuals<1 can straddle groups. At least3saturated, soTLS>=3.",
        "s_gt4": "within-group equal source/target distance>=1 gives (s-1)d>3>2. Atmostone residual<1 pergroup, soTLS>=4.",
    },
    "candidate_poses": poses,
    "classification": "Hand derivation: TLS=3 forces three exact inliers in one group. Noncollinear triple fixes positive scale and proper rigidpose; hence exactlytwo SO3 minimizers, boths1. O3 permits the two additional reflected minimizers. Classification bridge not yet kernel-accepted.",
    "threshold_mutation": {
        "epsilon": "15/2",
        "midpoint_tls": str(mid),
        "old_pose_tls": "3",
        "old_certificate_invalid": True,
    },
    "extra_correspondence": {
        "source": [0, 0, 2],
        "target": [0, 0, 2],
        "identity_tls": str(a),
        "translated_tls": str(b),
        "reflected_tls": str(mirror),
        "deduction": "Same pair certificates extend to groups4+3. TLS=3 forces allfour A points exact, an affinebasis; uniqueidentity evenifO3 allowed. This is objective uniqueness, not truthful acquisition without provenance/outlier assumptions.",
    },
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(
    json.dumps(
        {
            "two_proper_candidates": poses[:2],
            "epsilon_mutation": result["threshold_mutation"],
            "extra": result["extra_correspondence"],
        },
        indent=2,
    )
)
