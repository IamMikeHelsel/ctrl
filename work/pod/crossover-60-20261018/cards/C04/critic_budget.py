"""Exact face/slope and noncircular two-pass mixed-age screens; not execution proofs."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
R = F(2221, 40000)
K = F(9, 200)
drift = F(3, 1700)
noise = F(103, 1000)
D = F(1, 2000)
weights = [F(51, 50), F(101, 100), F(1)]


def z3(r, z, w):
    return (4 - r / 2) * z[0] + (-12 + 3 * r / 2) * z[1] + (8 - 3 * r / 2) * z[2] + r * w / 16


def slope(r, z, w):
    return (4 * r - 64) * z[0] + (160 - 12 * r) * z[1] + (12 * r - 96) * z[2] - r * w / 2


outer = 8 * R / 3
plateau = 38 * K / 15
shrink = (F(19, 10) * K - drift) * 4 / 3
for r in [F(8), F(12)]:
    for signs in product([-1, 1], repeat=2):
        for w in [-outer, outer]:
            assert z3(r, [signs[0] * R, signs[1] * R, R], w) <= 0
            assert z3(r, [-signs[0] * R, -signs[1] * R, -R], -w) >= 0
assert z3(F(12), [-R, R, R], outer + F(1, 10000)) > 0
assert z3(F(12), [-weights[0] * K, weights[1] * K, K], plateau) == 0
assert z3(F(12), [-weights[0] * K, weights[1] * K, K], shrink) == -drift
assert z3(F(12), [-weights[0] * K, weights[1] * K, K], outer) > 0
coarse = 48 * R + noise
L0 = 96 * R + 6 * coarse
rows = []
for A in [F(1, 1000), F(1, 800), F(3, 2000), F(3, 500)]:
    W1 = noise + max(F(8), L0) * A
    L1 = max(96 * R + 4 * W1, 80 * R + 6 * W1)
    W2 = noise + L1 * A + max(F(0), 8 - L1) * min(A, D)
    exact = max(
        abs(slope(r, [s * R for s in signs], w))
        for r, signs, w in product([F(8), F(12)], product([-1, 1], repeat=3), [-W1, W1])
    )
    assert exact == L1
    rows.append(
        {
            "age": str(A),
            "first_pass": str(W1),
            "digital_slope_after_first": str(L1),
            "mixed_second_pass": str(W2),
            "old_cube_possible": W2 < outer,
            "weighted_plateau_budget": W2 < plateau,
            "same_shrink_drift_budget": W2 < shrink,
        }
    )
result = {
    "outer_cube_ceiling": str(outer),
    "weighted_plateau_ceiling": str(plateau),
    "same_drift_ceiling": str(shrink),
    "outer_ceiling_weighted_face_outward_derivative": str(
        z3(F(12), [-weights[0] * K, weights[1] * K, K], outer)
    ),
    "coarse_mismatch": str(coarse),
    "coarse_slope": str(L0),
    "age_screens": rows,
    "scope": "Conditional finite-prefix bootstrap arithmetic; preserve C5 center/guard/weighted geometry. A completed first-exit and digital execution theorem is still needed. No unsafe digital trajectory inferred from independent residual vertex.",
}
(HERE / "critic_budget.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
