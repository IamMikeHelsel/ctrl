"""Exact vertex and two-pass audit; isolated, no producer imports."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

out = Path(__file__).with_name("domain_exact_results.json")
p, q, h = F(16, 3), F(6), F(1, 2)
weights = (F(51, 50), F(101, 100), F(1))
M = F(301, 3000)
checks = 0
rows = []
for K in (F(9, 200), F(2407079, 50250000), F(1, 20)):
    W = F(394, 75) * K
    B = (-p + 4 * q - 16 * h, -4 * q + 32 * h, -16 * h)
    max_slope = F(0)
    max_cmd = F(0)
    max_face = None
    for r in (F(8), F(12)):
        A = (4 + r * (B[0] - 16) / 16, -12 + r * (B[1] + 32) / 16, 8 + r * (B[2] - 16) / 16)
        for signs in itertools.product((-1, 1), repeat=4):
            z = tuple(s * wgt * K for s, wgt in zip(signs[:3], weights, strict=True))
            w = signs[3] * W
            x, v, a = z[0], 4 * (z[1] - z[0]), 16 * (z[0] - 2 * z[1] + z[2])
            u = -p * x - q * v - h * a
            adot = r * (u + w - a)
            zdot = v + a / 2 + adot / 16
            assert zdot == sum(ai * zi for ai, zi in zip(A, z, strict=True)) + r * w / 16
            slope = -p * v - q * a - h * adot
            C = (
                4 * p - 16 * q - h * r * (B[0] - 16),
                -4 * p + 32 * q - h * r * (B[1] + 32),
                -16 * q - h * r * (B[2] - 16),
            )
            assert slope == sum(ci * zi for ci, zi in zip(C, z, strict=True)) - h * r * w
            max_slope = max(max_slope, abs(slope))
            max_cmd = max(max_cmd, abs(u))
            if signs[2] == 1:
                max_face = zdot if max_face is None else max(max_face, zdot)
                assert zdot <= 0
            checks += 1
    assert max_cmd == F(674, 25) * K
    assert max_slope == max(F(9736, 75) * K + 4 * W, F(8884, 75) * K + 6 * W)
    age_rows = []
    for age in (F(1, 1000), F(16, 1000), F(18, 1000)):
        W0 = F(1348, 25) * K + M
        L0 = max(F(8), F(9736, 75) * K + 4 * W0, F(8884, 75) * K + 6 * W0)
        W1 = M + age * L0
        L1 = max(F(8), F(9736, 75) * K + 4 * W1, F(8884, 75) * K + 6 * W1)
        W2 = M + age * L1
        if age == F(16, 1000):
            assert W2 < W
        age_rows.append(
            {
                "age": str(age),
                "W0": str(W0),
                "L0": str(L0),
                "W1": str(W1),
                "L1": str(L1),
                "W2": str(W2),
                "slack": str(W - W2),
                "sufficient_budget_pass": W2 < W,
            }
        )
    rows.append(
        {
            "K": str(K),
            "W_face_limit": str(W),
            "max_command": str(max_cmd),
            "max_slope_at_face_budget": str(max_slope),
            "maximum_upper_face": str(max_face),
            "age_rows": age_rows,
        }
    )
old_face = (
    F(-2) * (-weights[0] * F(9, 200))
    + 6 * weights[1] * F(9, 200)
    - 10 * F(9, 200)
    + F(3, 4) * F(234, 1000)
)
assert old_face > 0
result = {
    "vertex_identity_checks": checks,
    "gain": [str(p), str(q), str(h)],
    "rows": rows,
    "negative_control_baseline_face_at_W234": str(old_face),
    "scope": "Exact algebra and sufficient budget, not a trajectory/execution or physical proof.",
}
out.write_text(json.dumps(result, indent=2) + "\n")
print(
    {
        "vertex_checks": checks,
        "old_gain_positive_face": str(old_face),
        "sixteen_ms_all_three_K_pass": True,
    }
)
