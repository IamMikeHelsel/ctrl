"""Independent certificate consumer; no producer imports. AI-written."""

import json
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent
report = json.loads((ROOT / "critic_overflow_results.json").read_text())
P = 18446744073708551616
Q = 1000000
LIMIT = 2**128
assert int(report["P0"]) == P and report["Q_max"] == Q
expected = [(206222625, 677376000, 16670745700, 11), (24561225, 115706752, 564578560, 1)]
checks = []
for record, (base, other, largest, cap) in zip(report["classes"], expected, strict=True):
    assert (record["base"], record["other"], record["max_N"], record["amax"]) == (
        base,
        other,
        largest,
        cap,
    )
    assert P * P + 4 * largest * Q * Q < LIMIT
    assert base * Q * Q // P == cap
    assert [c["a"] for c in record["certificates"]] == list(range(1, cap + 1))
    for cert in record["certificates"]:
        a = cert["a"]
        lo, hi = cert["b_lower"], cert["b_upper"]
        r = F(other * a, base)
        assert lo + 1 == hi and lo < r <= hi

        def residual(b, other=other, a=a, base=base, r=r):
            return F(b * b) - F(other * a * a, base) + (b - r) * P

        assert residual(lo) < 0 < residual(hi)
        assert residual(lo) == F(cert["f_lower_at_P0"])
        assert residual(hi) == F(cert["f_upper_at_P0"])
        assert F(cert["lower_slope"]) == lo - r < 0
        assert F(cert["upper_slope"]) == hi - r >= 0
        checks.append(
            {"base": base, "a": a, "lower": str(residual(lo)), "upper": str(residual(hi))}
        )
# Lowering the threshold to zero must not be inferred from those bounds.
p = F(7127, 355)
assert F(3) * (3 + p) == F(677376000, 206222625) * (1 + p)
assert p < P
# Safety cap mutations really would lose the final unsafe factor class.
assert expected[0][0] * Q * Q // P == 11 > 10
assert expected[1][0] * Q * Q // P == 1 > 0
result = {
    "branches_independently_replayed": len(checks),
    "checks": checks,
    "negative_controls": [
        "threshold zero has exact root b=3,p=7127/355",
        "omitting final first-class factor rejected",
        "omitting second-class factor rejected",
    ],
    "scope": "Arithmetic coverage repair only; no original execution, row-search, or unbounded completeness certification.",
}
(ROOT / "pm_overflow_check.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"branches": len(checks), "negative_controls": 3}))
