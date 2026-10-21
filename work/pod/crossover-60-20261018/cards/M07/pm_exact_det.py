"""Fraction-free elimination on graph components, independent of fixture factors."""

import json
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent


def parity(seq):
    return (-1) ** sum(x > y for i, x in enumerate(seq) for y in seq[i + 1 :])


def bareiss(a):
    a = [row[:] for row in a]
    n = len(a)
    sgn = 1
    den = 1
    for k in range(n - 1):
        if not a[k][k]:
            r = next((r for r in range(k + 1, n) if a[r][k]), None)
            if r is None:
                return 0
            a[r], a[k] = a[k], a[r]
            sgn = -sgn
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = a[i][j] * pivot - a[i][k] * a[k][j]
                assert num % den == 0
                a[i][j] = num // den
            a[i][k] = 0
        den = pivot
    return sgn * a[-1][-1] if n else 1


def components(rows, n):
    adj = [set() for _ in range(2 * n)]
    for i, row in enumerate(rows):
        for j, v in row.items():
            if v:
                adj[i].add(n + j)
                adj[n + j].add(i)
    seen = set()
    groups = []
    for x in range(2 * n):
        if x in seen:
            continue
        todo = [x]
        seen.add(x)
        g = []
        while todo:
            v = todo.pop()
            g.append(v)
            for w in adj[v] - seen:
                seen.add(w)
                todo.append(w)
        groups.append((sorted(v for v in g if v < n), sorted(v - n for v in g if v >= n)))
    return groups


if __name__ == "__main__":
    results = []
    fixtures = json.loads(
        Path(
            "/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/gu-source-exploration-20261018/software/thesis-appendix/determinant-fixtures.json"
        ).read_text()
    )["fixtures"]
    for fixture in fixtures:
        label = fixture["label"]
        data = json.loads((P / f"pm_matrix_{label.replace('.', '_')}.json").read_text())
        n = data["dimension"]
        rows = [{int(j): int(F(v)) for j, v in r} for r in data["rows"]]
        assert all(F(v).denominator == 1 for r in data["rows"] for _, v in r)
        groups = components(rows, n)
        dets = []
        for rs, cs in groups:
            if len(rs) != len(cs):
                dets.append(0)
            else:
                dets.append(bareiss([[rows[r].get(c, 0) for c in cs] for r in rs]))
        rp = [r for rs, _ in groups for r in rs]
        cp = [c for _, cs in groups for c in cs]
        value = parity(rp) * parity(cp)
        for d in dets:
            value *= d
        expected = fixture["determinant_sign"]
        for p, e in fixture["prime_factorization_abs"].items():
            expected *= int(p) ** e
        result = {
            "label": label,
            "component_sizes": dict(Counter(f"{len(r)}x{len(c)}" for r, c in groups)),
            "determinant": str(value),
            "expected_determinant": str(expected),
            "exact_match": value == expected,
            "absolute_match": abs(value) == abs(expected),
            "ratio": str(F(value, expected)) if expected else None,
            "block_determinants": [str(d) for d in dets],
            "row_permutation_sign": parity(rp),
            "column_permutation_sign": parity(cp),
        }
        results.append(result)
        print(label, result["component_sizes"], result["exact_match"], result["ratio"], flush=True)
        (P / "pm_exact_det.json").write_text(json.dumps(results, indent=2) + "\n")
