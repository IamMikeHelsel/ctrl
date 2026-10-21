"""Exact added states for the strict E12 capsule superset."""

import json
from fractions import Fraction as F
from pathlib import Path

P = [
    [F(38, 5), F(257, 25), F(5)],
    [F(257, 25), F(1319, 50), F(769, 50)],
    [F(5), F(769, 50), F(278, 25)],
]


def V(z):
    return sum(P[i][j] * z[i] * z[j] for i in range(3) for j in range(3))


n = [1, -1, 1]
pk = [F(189175, 11131832), F(-317075, 5565916), F(-302525, 2782958)]
g = F(4133475, 11131832)
base = [F(3, 2) * a / g + F(5, 4) * b for a, b in zip(pk, n, strict=True)]
z = [a + F(1, 25) * b for a, b in zip(base, n, strict=True)]
assert V(base) < 12 < V(z)
assert -z[0] - 3 * z[1] - 2 * z[2] == F(3, 2)
b0 = [F(17817, 10000) * a for a in n]
z0 = [F(18217, 10000) * a for a in n]
assert V(b0) < 12 and V(z0) > F(44527328, 3550075)
assert 12 * F(3550075, 11131832) < F(49, 25) ** 2
out = {
    "shape": "E12 + [-1/25,1/25]*(1,-1,1)",
    "strict_superset_reason": "Every E12 state uses hidden0; additional exact states below",
    "active_added": {
        "base": list(map(str, base)),
        "base_energy": str(V(base)),
        "state": list(map(str, z)),
        "energy": str(V(z)),
        "request": "3/2",
    },
    "beyond_Rstar": {
        "base": list(map(str, b0)),
        "base_energy": str(V(b0)),
        "state": list(map(str, z0)),
        "energy": str(V(z0)),
    },
    "position_margin": "49/25+1/25=2",
    "scope": "Same normalized lag and held h,w. Source E12 proof already exists; exact hidden lift and recursion bridge separately required.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print("Strict E12 inclusion and two added-state witnesses checked")
