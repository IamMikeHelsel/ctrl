"""Exact witness and symmetry checks for the prospective hidden-mode capsule."""

import json
from fractions import Fraction as F
from pathlib import Path

p = Path(__file__).resolve().parent
P = [
    [F(38, 5), F(257, 25), F(5)],
    [F(257, 25), F(1319, 50), F(769, 50)],
    [F(5), F(769, 50), F(278, 25)],
]


def V(z):
    return sum(z[i] * P[i][j] * z[j] for i in range(3) for j in range(3))


def request(z):
    return -z[0] - 3 * z[1] - 2 * z[2]


def flow(z, u, t, e):
    x, v, a = z
    return [
        x + t * v + u * t * t / 2 + (a - u) * (t - 1 + e),
        v + u * t + (a - u) * (1 - e),
        u + (a - u) * e,
    ]


g = F(4133475, 11131832)
pk = [F(189175, 11131832), F(-317075, 5565916), F(-302525, 2782958)]
n = [F(1), F(-1), F(1)]
base = [F(3, 2) * a / g + F(113, 100) * b for a, b in zip(pk, n, strict=True)]
z = [a + F(1, 8) * b for a, b in zip(base, n, strict=True)]
assert V(base) < 11 and V(z) > 12 and request(base) == request(z) == F(3, 2)
# Pure hidden capsule point exceeds even the maximal whole ellipsoid for travel2.
base_hidden = [F(17, 10) * a for a in n]
expanded_hidden = [F(73, 40) * a for a in n]
assert V(base_hidden) < 11 and V(expanded_hidden) > F(44527328, 3550075)
for state in [base, [F(0), F(1, 10), F(2, 5)]]:
    for d in [F(-1, 8), F(1, 8)]:
        shifted = [a + d * b for a, b in zip(state, n, strict=True)]
        assert request(state) == request(shifted)
        for w in [F(-1, 100), F(1, 100)]:
            u = max(-F(1), min(F(1), request(state))) + w
            for t, e in [(F(1, 5), F(4, 5)), (F(1, 10), F(9, 10))]:
                lhs = flow(shifted, u, t, e)
                rhs = flow(state, u, t, e)
                assert lhs == [a + d * e * b for a, b in zip(rhs, n, strict=True)]
# Changing rate destroys exact hidden derivative invariance even with same clamp.
rate = F(2)
d = F(1, 8)
quotient_gap = (1 - rate) * d
assert quotient_gap == -F(1, 8)
lost = [F(41, 20) * a / g for a in pk]
assert 11 < V(lost) < 12 and request(lost) ** 2 > 11 * g
out = {
    "old_E12_point_outside_capsule": {
        "state": list(map(str, lost)),
        "energy": str(V(lost)),
        "request": str(request(lost)),
        "reason": "request squared exceeds11*kappa; hidden shift cannot change request",
    },
    "active_outside_E12": {
        "base": list(map(str, base)),
        "base_energy": str(V(base)),
        "state": list(map(str, z)),
        "state_energy": str(V(z)),
        "request": str(request(z)),
    },
    "hidden_outside_Rstar": {
        "state": list(map(str, expanded_hidden)),
        "energy": str(V(expanded_hidden)),
    },
    "lag_rate2_quotient_derivative_gap": str(quotient_gap),
    "scope": "Hand lifted invariant needs E11 source wrapper and recursion; same disturbance/clock and normalized rate exactly1. No variable-rate or physical claim.",
}
(p / "critic_capsule.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
