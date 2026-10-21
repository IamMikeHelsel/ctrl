"""Independent rational boundary-point and projective reduction verification."""

import json
from fractions import Fraction as F
from math import gcd, isqrt, lcm
from pathlib import Path

P = Path(__file__).parent
data = json.loads((P / "inventor_elliptic.json").read_text())
src = json.loads((P / "inventor_infinity.json").read_text())
a = [F(4 * n) for n in data["original_Ns"]]
known = [tuple(map(F, r["point"])) for r in data["known_column_lifts"]]


def plus(u, v):
    x, y = u
    z, t = v
    slope = (
        (3 * x * x + 2 * sum(a[:3]) * x + (a[0] * a[1] + a[0] * a[2] + a[1] * a[2])) / (2 * y)
        if u == v
        else (t - y) / (z - x)
    )
    X = slope * slope - sum(a[:3]) - x - z
    return X, -y + slope * (x - X)


q = known[1]
for operand, step in zip(
    [known[1], known[3], (known[2][0], -known[2][1])], src["chord_steps"], strict=True
):
    q = plus(q, operand)
    assert q == tuple(map(F, step["point"]))
    assert [F(z) ** 2 for z in step["roots"]] == [q[0] + v for v in a[:3]]
    m, c = F(step["slope"]), F(step["intercept"])
    assert q[1] == -(m * q[0] + c)
assert q == tuple(map(F, src["point"]))
x, y = q
assert y * y == (x + a[0]) * (x + a[1]) * (x + a[2])
den = lcm(x.denominator, y.denominator)
coords = [x.numerator * (den // x.denominator), y.numerator * (den // y.denominator), den]
g = gcd(gcd(abs(coords[0]), abs(coords[1])), coords[2])
coords = [v // g for v in coords]
assert coords == src["primitive_projective_coordinates"]
assert [v % 197 for v in coords] == [0, 160, 0] == src["projective_reduction"]
# Affine-only modular inversion is impossible despite this valid rational point.
assert x.denominator % 197 == 0 and y.denominator % 197 == 0
assert isqrt(x.numerator) ** 2 != x.numerator or isqrt(x.denominator) ** 2 != x.denominator
assert [0, 160, 0] != [0, 0, 1]
out = {
    "finite_rational_point_verified": True,
    "three_chord_steps_verified": True,
    "projective_reduction": [0, 160, 0],
    "full_column": False,
    "scope": "Valid partial lift that affine-only denominator filtering would discard; not a fifth column or omitted full solution.",
}
(P / "critic_infinity_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
