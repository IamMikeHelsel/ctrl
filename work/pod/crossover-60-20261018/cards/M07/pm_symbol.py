"""Source-map reconstruction; provisional signed-summand order, no expected values in map."""

import json
from fractions import Fraction as F
from pathlib import Path

import domain_double as d

HERE = Path(__file__).resolve().parent
B = d.bases()


def inject(group, x, c):
    if group == "L1":
        return d.raise_(d.tensor(d.blade(), x))
    if group == "L3":
        z = d.tensor(d.blade(), x)
        return d.add(d.scale(c[0], d.map_right(d.raise_(z), d.cleavep)), d.scale(c[1], d.shift(z)))
    return x


def symbol(x, c, v=None):
    v = d.blade(1) if v is None else v
    bp = d.map_left(x, lambda a: d.add(d.wedge(v, a), d.interior(v, a)))
    out = [{}, {}, {}, {}]
    for (a, b), coef in bp.items():
        z = {(a, b): F(1)}
        n, m = len(a), len(b)
        if (n, m) == (2, 4):
            vals = [
                d.scale(c[2], d.i(d.flip(d.shift(d.flip(z))))),
                d.scale(c[5], d.projY(d.lower(z))),
                d.scale(c[7], d.i(z)),
                {},
            ]
        elif (n, m) == (2, 2):
            vals = [
                d.scale(c[3], d.cleavep(d.e(z))),
                d.scale(c[6], d.projY(d.flip(d.shift(z)))),
                d.scale(c[8], d.e(d.lower(z))),
                d.projY(d.lower(z)),
            ]
        elif (n, m) == (0, 4):
            vals = [d.scale(c[4], {b: F(1)}), {}, {}, {}]
        elif (n, m) == (0, 2):
            vals = [{}, {}, d.scale(c[9], {b: F(1)}), {}]
        else:
            raise ValueError((n, m))
        out = [d.add(old, d.scale(coef, val)) for old, val in zip(out, vals, strict=True)]
    return out


def matrix(c, covector=None):
    rows = []
    for group in ("L1", "L3", "Y2", "Y4p"):
        for x in B[group]:
            out = symbol(inject(group, x, c), c, covector)
            row = [
                2 * d.sp(y, t)
                for y, name in zip(out, ("L4p", "Y3", "L2", "Y1"), strict=True)
                for t in B[name]
            ]
            rows.append(row)
    return rows


def det_mod(a, p):
    a = [[int(x.numerator) * pow(x.denominator, -1, p) % p for x in row] for row in a]
    value = 1
    rank = 0
    n = len(a)
    for j in range(n):
        k = next((k for k in range(rank, n) if a[k][j]), None)
        if k is None:
            continue
        if k != rank:
            a[k], a[rank] = a[rank], a[k]
            value = -value
        pivot = a[rank][j]
        value = value * pivot % p
        inv = pow(pivot, -1, p)
        for k in range(rank + 1, n):
            if a[k][j]:
                fac = a[k][j] * inv % p
                a[k][j:] = [(x - fac * y) % p for x, y in zip(a[k][j:], a[rank][j:], strict=True)]
        rank += 1
    return {"rank": rank, "determinant": value % p if rank == n else 0}


if __name__ == "__main__":
    fixtures = json.loads(
        Path(
            "/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/gu-source-exploration-20261018/software/thesis-appendix/determinant-fixtures.json"
        ).read_text()
    )["fixtures"]
    results = []
    for f in fixtures:
        a = matrix(f["coefficients"])
        label = f["label"].replace(".", "_")
        sparse = [[[j, str(x)] for j, x in enumerate(row) if x] for row in a]
        (HERE / f"pm_matrix_{label}.json").write_text(
            json.dumps({"dimension": 448, "coefficients": f["coefficients"], "rows": sparse}) + "\n"
        )
        checks = {}
        for p in (101, 103):
            actual = det_mod(a, p)
            expected = f["determinant_sign"]
            for prime, exponent in f["prime_factorization_abs"].items():
                expected = expected * pow(int(prime), exponent, p) % p
            checks[str(p)] = {
                **actual,
                "expected_residue": expected % p,
                "matches": actual["determinant"] == expected % p,
                "absolute_sign_matches": actual["determinant"] in (expected % p, -expected % p),
            }
        result = {
            "label": f["label"],
            "nonzeros": sum(len(r) for r in sparse),
            "denominators": sorted({x.denominator for row in a for x in row}),
            "checks": checks,
        }
        results.append(result)
        (HERE / "pm_symbol_results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(result), flush=True)
