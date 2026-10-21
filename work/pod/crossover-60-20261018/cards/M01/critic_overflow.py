"""Exact finite square-gap certificates for all unsafe column-test branches.

No denominator scan and no source search modifications. Does not audit row extension.
"""

import json
from fractions import Fraction as F
from math import ceil
from pathlib import Path

P = Path(__file__).parent
Q = 10**6
U = 2**128 - 1
P0 = 2**64 - 10**6
classes = [
    ("first", 206222625, [206222625, 677376000, 2019635200, 4786481700, 16670745700]),
    ("second", 24561225, [10046592, 24561225, 115706752, 281637972, 564578560]),
]
reports = []
for name, base, ns in classes:
    largest = max(ns)
    # p<=P0 makes every relevant discriminant fit u128, including the addition.
    safe_upper = P0 * P0 + 4 * largest * Q * Q
    assert safe_upper <= U
    # If overflow is possible, p>P0; a(a+p)=base*q² then bounds a uniformly.
    amax = base * Q * Q // P0
    other = min(n for n in ns if n > base)
    ratio = F(other, base)
    certs = []
    for a in range(1, amax + 1):
        r = a * ratio
        lo = ceil(r) - 1
        hi = lo + 1

        # b(b+p)=ratio*a(a+p); polynomial is increasing for b>=0.
        def f_at(b, p, ratio=ratio, a=a, r=r):
            return b * b - ratio * a * a + (b - r) * p

        lower = f_at(lo, P0)
        upper = f_at(hi, P0)
        assert lo >= 0 and lo - r < 0 and hi - r >= 0
        assert lower < 0 < upper
        # Lower sign decreases and upper sign stays/increases for all p>=P0.
        # Unique positive real root lies strictly between adjacent integers.
        certs.append(
            {
                "a": a,
                "ratio_times_a": str(r),
                "b_lower": lo,
                "b_upper": hi,
                "f_lower_at_P0": str(lower),
                "f_upper_at_P0": str(upper),
                "lower_slope": str(lo - r),
                "upper_slope": str(hi - r),
            }
        )
    reports.append(
        {
            "class": name,
            "base": base,
            "other": other,
            "max_N": largest,
            "amax": amax,
            "u128_safety_margin": str(U - safe_upper),
            "certificates": certs,
        }
    )
assert [r["amax"] for r in reports] == [11, 1]
# Negative control: adjacent brackets must actually straddle the root.
c = reports[0]["certificates"][0]
assert F(c["f_lower_at_P0"]) < 0 and F(c["f_upper_at_P0"]) > 0
# Incorrectly moving both endpoints down or up loses one necessary sign.
a = 1
ratio = F(classes[0][2][1], classes[0][1])
r = a * ratio
lo = ceil(r) - 1


def poly(b):
    return b * b - ratio * a * a + (b - r) * P0


assert poly(lo - 1) < 0 and poly(lo) < 0
assert poly(lo + 1) > 0 and poly(lo + 2) > 0
result = {
    "Q_max": Q,
    "P0": str(P0),
    "classes": reports,
    "conclusion": "For these two classes and q<=1e6, every candidate capable of overflowing a column discriminant already fails an exact other-row square condition. This repairs the arithmetic gap analytically for the fixed range, not the original implementation or unbounded search.",
    "scope": "Rational inequality certificate checked by Python, not yet Lean; no row-extension bound or execution/coverage log certification.",
    "negative_bracket_mutations_rejected": 2,
}
(P / "critic_overflow_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(
    json.dumps(
        {
            "amax": [r["amax"] for r in reports],
            "certificates": sum(len(r["certificates"]) for r in reports),
            "P0": str(P0),
            "safe_margins": [r["u128_safety_margin"] for r in reports],
        }
    )
)
