"""Exact Gaussian-rational Clifford conjugation; no source gauge admissibility claim."""

import json
from fractions import Fraction as F
from pathlib import Path

from critic_operator import cliff


def cmul(x, y):
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c)


def mul(x, y):
    out = {}
    for a, v in x.items():
        for b, w in y.items():
            c, s = cliff(a, b)
            u = cmul(v, w)
            old = out.get(c, (F(0), F(0)))
            new = (old[0] + s * u[0], old[1] + s * u[1])
            if new != (0, 0):
                out[c] = new
            elif c in out:
                del out[c]
    return out


P = (0, 1, 2, 3)
g = {(): (F(3, 5), F(0)), P: (F(0), F(4, 5))}
gi = {(): (F(3, 5), F(0)), P: (F(0), F(-4, 5))}
assert mul(g, gi) == {(): (1, 0)} and mul(gi, g) == {(): (1, 0)}
e = mul(mul(gi, {(0,): (F(1), F(0))}), g)
assert e == {(0,): (F(-7, 25), F(0)), (1, 2, 3): (F(0), F(24, 25))}
q = mul(mul(gi, {(1, 2, 3, 4): (F(1), F(0))}), g)
assert set(map(len, q)) == {2, 4}
report = {
    "status": "pass",
    "vector_conjugate": str(e),
    "four_blade_conjugate": str(q),
    "scope": "Gaussian-rational Clifford algebra. Full source gauge admissibility requires separate adjoint/epsilon binding; fixed grade projectors do not commute with this algebra automorphism.",
    "covariance_boundary": "Conjugating every coefficient including Phi preserves multiplication and brackets; holding Phi fixed while changing only curvature is a different operation.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
