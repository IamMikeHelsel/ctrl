"""Exact tiny elliptic quotient experiment; not a denominator search."""

import json
from fractions import Fraction as F
from itertools import combinations
from math import isqrt
from pathlib import Path

GRIDS = [
    ([206222625, 677376000, 2019635200, 4786481700, 16670745700], [13440, 75936, 129360, 279840]),
    ([10046592, 24561225, 115706752, 281637972, 564578560], [5976, 10104, 24216, 69624]),
]


def sqrtq(x):
    x = F(x)
    if x < 0:
        return None
    a, b = isqrt(x.numerator), isqrt(x.denominator)
    return F(a, b) if a * a == x.numerator and b * b == x.denominator else None


def add(p, q, a, b):
    if p is None:
        return q
    if q is None:
        return p
    x, y = p
    z, t = q
    if x == z:
        if y != t or y == 0:
            return None
        m = (3 * x * x + 2 * a * x + b) / (2 * y)
    else:
        m = (t - y) / (z - x)
    xx = m * m - a - x - z
    yy = -y + m * (x - xx)
    assert yy * yy == xx * (xx * xx + a * xx + b)
    return xx, yy


def neg(p):
    return None if p is None else (p[0], -p[1])


def serial(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, (list, tuple)):
        return [serial(v) for v in x]
    if isinstance(x, dict):
        return {k: serial(v) for k, v in x.items()}
    return x


def check_grid(ns, ds):
    assert len(set(ns)) == 5 and min(ns) > 0
    assert len(set(ds)) == 4 and min(ds) > 0
    roots = [[sqrtq(4 * n + d * d) for d in ds] for n in [0, *ns]]
    assert all(r is not None for row in roots for r in row)
    factors = []
    for n, row in zip(ns, roots[1:], strict=True):
        ff = []
        for d, r in zip(ds, row, strict=True):
            lo, hi = (r - d) / 2, (r + d) / 2
            assert lo.denominator == hi.denominator == 1
            assert lo > 0 and lo * hi == n and hi - lo == d
            ff.append([lo, hi])
        factors.append(ff)
    a, b = F(4 * (ns[0] + ns[1])), F(16 * ns[0] * ns[1])
    points = [(F(d * d), F(d) * roots[1][j] * roots[2][j]) for j, d in enumerate(ds)]
    seeds = [(f"P{i}", p) for i, p in enumerate(points)]
    for i, j in combinations(range(4), 2):
        seeds.append((f"P{i}+P{j}", add(points[i], points[j], a, b)))
        seeds.append((f"P{i}-P{j}", add(points[i], neg(points[j]), a, b)))
    candidates = []
    for name, p in seeds:
        q = add(p, p, a, b)
        if q is None:
            candidates.append({"seed": name, "doubled": "infinity"})
            continue
        x, y = q
        first = [sqrtq(x + 4 * n) for n in [0, ns[0], ns[1]]]
        assert all(r is not None for r in first)
        remaining = [sqrtq(x + 4 * n) is not None for n in ns[2:]]
        # Independently check explicit lifting formula from the pre-doubling point.
        sx, sy = p
        aa, bb = F(4 * ns[0]), F(4 * ns[1])
        w_formula = (sx * sx - aa * bb) / (2 * sy)
        r1_formula = (sx * sx + 2 * aa * sx + aa * bb) / (2 * sy)
        r2_formula = (sx * sx + 2 * bb * sx + aa * bb) / (2 * sy)
        assert w_formula * w_formula == x
        assert r1_formula * r1_formula == x + aa
        assert r2_formula * r2_formula == x + bb
        certificates = []
        for n, works in zip(ns[2:], remaining, strict=True):
            if not works:
                value = x + 4 * n
                for component, integer in [
                    ("numerator", value.numerator),
                    ("denominator", value.denominator),
                ]:
                    floor = isqrt(integer)
                    if floor * floor != integer:
                        assert floor * floor < integer < (floor + 1) * (floor + 1)
                        certificates.append(
                            {
                                "N": n,
                                "nonsquare_component": component,
                                "integer": integer,
                                "floor_sqrt": floor,
                            }
                        )
                        break
        candidates.append(
            {
                "seed": name,
                "x": x,
                "y": y,
                "w": first[0],
                "first_three_roots": first,
                "remaining_square_tests": remaining,
                "rejection_certificates": certificates,
                "new_column": all(remaining) and first[0] not in ds,
                "known_column": first[0] in ds,
            }
        )
    return {
        "Ns": ns,
        "differences": ds,
        "roots_6_by_4": roots,
        "factor_witnesses_5_by_4": factors,
        "quotient": "y^2=x(x+4N0)(x+4N1)",
        "a2": a,
        "a4": b,
        "predetermined_candidates": candidates,
        "finite_candidate_count": len(candidates),
        "new_column_count": sum(c.get("new_column", False) for c in candidates),
        "known_column_count": sum(c.get("known_column", False) for c in candidates),
        "infinity_count": sum(c.get("doubled") == "infinity" for c in candidates),
    }


def main():
    results = [check_grid(ns, ds) for ns, ds in GRIDS]
    Path(__file__).with_name("domain_quotient_results.json").write_text(
        json.dumps(serial(results), indent=2) + "\n"
    )
    for result in results:
        print(
            {
                k: result[k]
                for k in [
                    "finite_candidate_count",
                    "new_column_count",
                    "known_column_count",
                    "infinity_count",
                ]
            }
        )


if __name__ == "__main__":
    main()
