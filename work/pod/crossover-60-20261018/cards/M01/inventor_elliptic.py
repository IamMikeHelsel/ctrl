"""Exact quotient-and-lift experiment; no denominator scan or solver calls."""

import json
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import isqrt
from pathlib import Path

NS = [206222625, 677376000, 2019635200, 4786481700, 16670745700]
COLUMNS = [13440, 75936, 129360, 279840]
A = [F(4 * n) for n in NS]
a2 = sum(A[:3])
a4 = A[0] * A[1] + A[0] * A[2] + A[1] * A[2]
a6 = A[0] * A[1] * A[2]


def rational_sqrt(x):
    x = F(x)
    if x < 0:
        return None
    p, q = isqrt(x.numerator), isqrt(x.denominator)
    return F(p, q) if p * p == x.numerator and q * q == x.denominator else None


def curve(x):
    return (x + A[0]) * (x + A[1]) * (x + A[2])


def on_curve(point):
    return point is None or point[1] ** 2 == curve(point[0])


def add(p, q):
    if p is None:
        return q
    if q is None:
        return p
    x, y = p
    z, v = q
    if x == z and y == -v:
        return None
    slope = (3 * x * x + 2 * a2 * x + a4) / (2 * y) if p == q else (v - y) / (z - x)
    X = slope * slope - a2 - x - z
    Y = -y + slope * (x - X)
    result = (X, Y)
    assert on_curve(result)
    return result


def lift(point):
    if point is None:
        return {"status": "POINT_AT_INFINITY"}
    x, y = point
    factors = [rational_sqrt(x + a) for a in A]
    w = rational_sqrt(x)
    return {
        "point": point,
        "quotient_equation_exact": y * y == curve(x),
        "positive_X": x > 0,
        "X_square": w is not None,
        "w": w,
        "factor_square_mask": [r is not None for r in factors],
        "roots": factors,
        "new_column": x > 0
        and w is not None
        and all(r is not None for r in factors)
        and w not in COLUMNS,
    }


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, (list, tuple)):
        return [encode(v) for v in x]
    if isinstance(x, dict):
        return {k: encode(v) for k, v in x.items()}
    return x


known = []
for w in COLUMNS:
    x = F(w * w)
    roots = [rational_sqrt(x + a) for a in A]
    assert all(r is not None for r in roots)
    point = (x, roots[0] * roots[1] * roots[2])
    assert on_curve(point)
    known.append(point)
records = []
chord_lift_certificates = []
for i, j in combinations_with_replacement(range(4), 2):
    for sign in [1, -1]:
        q = (known[j][0], sign * known[j][1])
        point = add(known[i], q)
        entry = lift(point)
        entry["operation"] = f"P{i + 1}{'+' if sign == 1 else '-'}P{j + 1}"
        records.append(entry)
        if point is not None:
            x, y = known[i]
            z, v = q
            slope = (3 * x * x + 2 * a2 * x + a4) / (2 * y) if known[i] == q else (v - y) / (z - x)
            intercept = y - slope * x
            X = point[0]
            assert x + z + X == slope * slope - a2
            assert x * z + x * X + z * X == a4 - 2 * slope * intercept
            assert x * z * X == intercept * intercept - a6
            derived_roots = []
            for ai in A[:3]:
                si, sj = rational_sqrt(x + ai), rational_sqrt(z + ai)
                assert si is not None and sj is not None and si * sj != 0
                root = (intercept - slope * ai) / (si * sj)
                assert root * root == X + ai
                derived_roots.append(root)
            chord_lift_certificates.append(
                {
                    "operation": entry["operation"],
                    "slope": slope,
                    "intercept": intercept,
                    "derived_first_three_roots": derived_roots,
                    "factor_polynomial_identity_checked": True,
                }
            )
for i, p in enumerate(known):
    for j in range(3):
        point = add(p, (-A[j], F(0)))
        entry = lift(point)
        entry["operation"] = f"P{i + 1}+T{j + 1}"
        records.append(entry)
finite = [r for r in records if "point" in r]
summary = {
    "operations": len(records),
    "finite_points": len(finite),
    "unique_finite_X": len({r["point"][0] for r in finite}),
    "three_quotient_factors_square": sum(all(r["factor_square_mask"][:3]) for r in finite),
    "X_square": sum(r["X_square"] for r in finite),
    "all_five_factors_square": sum(all(r["factor_square_mask"]) for r in finite),
    "new_complete_columns": sum(r["new_column"] for r in finite),
}
assert not any(r["new_column"] for r in finite)
assert any(all(r["factor_square_mask"][:3]) and not r["X_square"] for r in finite)
assert any(not all(r["factor_square_mask"][:3]) for r in finite)
assert add(known[1], known[2]) == known[0]
result = {
    "original_Ns": NS,
    "original_columns": COLUMNS,
    "known_column_lifts": [lift(p) for p in known],
    "quotient": "Y^2=(X+4N1)(X+4N2)(X+4N3), X=w^2; remaining conditions retained separately.",
    "summary": summary,
    "exact_operation_records": records,
    "known_group_relation": "P1=P2+P3, with positiveY lifts corresponding to columns13440,75936,129360.",
    "chord_lift_certificates": chord_lift_certificates,
    "scope": "Small structured elliptic group-law orbit of existing points plus rational2-torsion. Exact rational curve identities and square tests; not full Mordell-Weil computation, 2-descent proof, search completeness, or nonextension theorem.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(encode(result), indent=2) + "\n")
print(json.dumps(summary, indent=2))
for r in finite:
    if all(r["factor_square_mask"][:3]) and not r["X_square"]:
        print("quotient_lift_failure", r["operation"], str(r["point"][0]), r["factor_square_mask"])
        break
