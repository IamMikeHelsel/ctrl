"""Independent exact physical-coordinate audit of proposed C04 gain/age budgets."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
P, Q, H = F(16, 3), F(6), F(1, 2)
R, TARGET, DRIFT = F(2221, 40000), F(9, 200), F(3, 1700)
WEIGHTS = (F(51, 50), F(101, 100), F(1))
M = P / 1000 + Q / 100 + H / 20 + F(1, 100)


def physical(z, rate, residual):
    x, v, a = z[0], 4 * (z[1] - z[0]), 16 * (z[0] - 2 * z[1] + z[2])
    k = -P * x - Q * v - H * a
    jerk = rate * (k + residual - a)
    return (v, v + a / 4, v + a / 2 + jerk / 16), -P * v - Q * a - H * jerk


pending = max(
    abs(-P * v - Q * a - H * r * (-F(121, 100) + d - a))
    for r, v, a, d in product(
        (F(8), F(12)),
        (-F(1533, 50000), F(1533, 50000)),
        (-F(33, 25), F(33, 25)),
        (-F(1, 100), F(1, 100)),
    )
)
assert pending < 8
command = F(80, 3) * R
coarse = 2 * command + M
rows = []
for age in (F(3, 200), F(2, 125), F(1, 25)):
    w = coarse
    passes = []
    for _ in range(3):
        slope = max(
            abs(physical(tuple(s * R for s in signs), r, wr)[1])
            for r, signs, wr in product((F(8), F(12)), product((-1, 1), repeat=3), (-w, w))
        )
        assert slope == max(128 * R + 4 * w, F(352, 3) * R + 6 * w)
        w = M + age * max(pending, slope)
        passes.append(str(w))
    max_faces = []
    for i in range(3):
        face = []
        for r, signs in product((F(8), F(12)), product((-1, 1), repeat=3)):
            if signs[i] != 1:
                continue
            z = tuple(signs[j] * WEIGHTS[j] * TARGET for j in range(3))
            for wr in (-w, w):
                dz, _ = physical(z, r, wr)
                face.append(dz[i] + WEIGHTS[i] * DRIFT)
        max_faces.append(max(face))
    rows.append(
        {
            "age": str(age),
            "passes": passes,
            "weighted_shrink_face_maxima": list(map(str, max_faces)),
            "accepted_arithmetic": max(max_faces) <= 0,
        }
    )
assert rows[0]["accepted_arithmetic"]
assert not rows[-1]["accepted_arithmetic"]
# Exact necessity mutation: exceeding the third face threshold fails at rate12.
limit = (F(197, 50) * TARGET - DRIFT) * F(4, 3)
z = tuple(w * TARGET for w in WEIGHTS)
assert physical(z, F(12), limit)[0][2] == -DRIFT
assert physical(z, F(12), limit + F(1, 10000))[0][2] > -DRIFT
# A stale sample before time zero is not covered by any forward prefix argument.
assert F(-1, 1000) < 0
result = {
    "pending_max_correct_original_bounds": str(pending),
    "sensor_plus_target_error": str(M),
    "coarse_residual": str(coarse),
    "measured_command_bound": str(command + M - F(1, 100)),
    "weighted_shrink_limit": str(limit),
    "cases": rows,
    "negative_controls": ["40ms fails arithmetic", "excess residual violates weighted face"],
    "scope": "Exact conditional prefix arithmetic, independently using physical dynamics; not an execution or first-exit proof.",
}
(HERE / "critic_codesign.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
