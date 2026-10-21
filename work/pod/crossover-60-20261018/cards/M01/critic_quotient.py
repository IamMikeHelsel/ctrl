"""Independent quotient/lift and bounded-candidate certificate audit."""

import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path

P = Path(__file__).parent
reports = json.loads((P / "domain_quotient_results.json").read_text())
results = []
for item in reports:
    ns, ds = item["Ns"], item["differences"]
    assert len(set(ns)) == 5 and min(ns) > 0 and len(set(ds)) == 4 and min(ds) > 0
    roots = [[F(v) for v in row] for row in item["roots_6_by_4"]]
    for n, row in zip([0, *ns], roots, strict=True):
        for d, r in zip(ds, row, strict=True):
            assert r > 0 and r * r == d * d + 4 * n
    # Rational-to-integer clearing: scaled old columns preserve positive factors.
    for n in ns:
        for d in ds:
            q = 7
            s = q * isqrt(d * d + 4 * n)
            p = q * d
            assert (s - p) % 2 == 0 and (s - p) // 2 > 0
            assert ((s - p) // 2) * ((s + p) // 2) == n * q * q
    aa, bb = F(4 * ns[0]), F(4 * ns[1])
    # Nonzero positive-x quotient point from known P plus rational2-torsion(0,0).
    x = F(ds[0] ** 2)
    y = F(ds[0]) * roots[1][0] * roots[2][0]
    xx = aa * bb / x
    yy = -aa * bb * y / (x * x)
    assert xx > 0 and yy != 0 and yy * yy == xx * (xx + aa) * (xx + bb)
    assert isqrt(xx.numerator) ** 2 != xx.numerator or isqrt(xx.denominator) ** 2 != xx.denominator
    # Curve validity alone therefore does not supply rational w with w²=x.
    xs = set()
    cert_count = 0
    for c in item["predetermined_candidates"]:
        assert c.get("doubled") != "infinity"
        x, y, w = F(c["x"]), F(c["y"]), F(c["w"])
        assert x not in xs
        xs.add(x)
        assert w > 0 and w not in ds and w * w == x
        assert y * y == x * (x + aa) * (x + bb)
        supplied = [F(z) for z in c["first_three_roots"]]
        assert [r * r for r in supplied] == [x, x + aa, x + bb]
        assert c["remaining_square_tests"] == [False] * 3
        assert len(c["rejection_certificates"]) == 3
        for cert, n in zip(c["rejection_certificates"], ns[2:], strict=True):
            value = x + 4 * n
            assert cert["N"] == n
            integer = getattr(value, cert["nonsquare_component"])
            lower = cert["floor_sqrt"]
            assert integer == cert["integer"] and lower * lower < integer < (lower + 1) ** 2
            # Corrupted floor and denominator-component choice must not be trusted.
            assert not ((lower + 1) ** 2 < integer < (lower + 2) ** 2)
            cert_count += 1
    results.append(
        {
            "Ns": ns,
            "positive_quotient_nonlift": {"x": str(xx), "y": str(yy)},
            "distinct_candidates_checked": len(xs),
            "floor_square_certificates_checked": cert_count,
            "new_extensions": 0,
        }
    )
assert sum(r["distinct_candidates_checked"] for r in results) == 32
(P / "critic_quotient_results.json").write_text(json.dumps(results, indent=2) + "\n")
print(
    json.dumps(
        [
            {
                "candidates": r["distinct_candidates_checked"],
                "certificates": r["floor_square_certificates_checked"],
            }
            for r in results
        ]
    )
)
