"""Independent exact checks for the alternate quotient and chord certificates."""

import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path

P = Path(__file__).parent
src = json.loads((P / "inventor_elliptic.json").read_text())
ns = src["original_Ns"]
a = [F(4 * n) for n in ns]


def square(v):
    return (
        v >= 0
        and isqrt(v.numerator) ** 2 == v.numerator
        and isqrt(v.denominator) ** 2 == v.denominator
    )


known = [tuple(map(F, r["point"])) for r in src["known_column_lifts"]]
finite = [r for r in src["exact_operation_records"] if "point" in r]
by_name = {r["operation"]: r for r in finite}
for r in finite:
    x, y = map(F, r["point"])
    assert y * y == (x + a[0]) * (x + a[1]) * (x + a[2])
    assert r["X_square"] == square(x)
    assert r["factor_square_mask"] == [square(x + v) for v in a]
    if r["X_square"]:
        assert F(r["w"]) ** 2 == x
    assert not r["new_column"]
for cert in src["chord_lift_certificates"]:
    x, y = map(F, by_name[cert["operation"]]["point"])
    m, c = F(cert["slope"]), F(cert["intercept"])
    roots = list(map(F, cert["derived_first_three_roots"]))
    assert [r * r for r in roots] == [x + v for v in a[:3]]
    # Returned group point is reflected across the chord line.
    assert y == -(m * x + c)
# Important relation: four saved points do not imply four independent generators.
x, y = known[1]
z, v = known[2]
m = (v - y) / (z - x)
xx = m * m - sum(a[:3]) - x - z
yy = -y + m * (x - xx)
assert (xx, yy) == known[0]
# Negative certificate controls: altered point y and any nonzero-root magnitude fail.
x, y = known[0]
assert (y + 1) ** 2 != (x + a[0]) * (x + a[1]) * (x + a[2])
example = src["chord_lift_certificates"][0]
r = abs(F(example["derived_first_three_roots"][0]))
X = F(by_name[example["operation"]]["point"][0])
assert (r + 1) ** 2 != X + a[0]
out = {
    "finite_points_checked": len(finite),
    "chord_lift_certificates_checked": len(src["chord_lift_certificates"]),
    "known_relation": "P1=P2+P3 verified",
    "complete_new_columns": 0,
    "negative_controls": 2,
    "scope": "Finite point/certificate replay, not full rational-point enumeration or Mordell-Weil independence/rank proof.",
}
(P / "critic_chords_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
