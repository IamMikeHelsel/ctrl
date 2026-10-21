"""Predetermined exact correspondence-rank tests, including critical nonplanarity."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def rank(rows):
    a = [list(row) for row in rows]
    pivots = []
    lead = 0
    for col in range(len(a[0])):
        candidates = [i for i in range(lead, len(a)) if a[i][col]]
        if not candidates:
            continue
        pivot = candidates[0]
        a[lead], a[pivot] = a[pivot], a[lead]
        divisor = a[lead][col]
        a[lead] = [value / divisor for value in a[lead]]
        for i in range(len(a)):
            if i == lead:
                continue
            weight = a[i][col]
            a[i] = [x - weight * y for x, y in zip(a[i], a[lead], strict=True)]
        pivots.append(col)
        lead += 1
        if lead == len(a):
            break
    return len(pivots), pivots, a


def correspondence(u, v, depth):
    assert depth > 0
    return ([u, v, F(1)], [u + 1 / depth, v, F(1)])


def design(pairs):
    return [[y[i] * x[j] for i in range(3) for j in range(3)] for x, y in pairs]


def main():
    if not __debug__:
        raise RuntimeError("Do not run with -O")
    grid = [
        correspondence(u, v, F(1)) for u in [F(0), F(1, 2), F(1)] for v in [F(0), F(1, 2), F(1)]
    ]
    critical = correspondence(F(1, 4), F(0), F(3, 2))
    separating1 = correspondence(F(1, 4), F(1, 4), F(2))
    separating2 = correspondence(F(1, 4), F(3, 4), F(2))
    cases = [
        ("plane_only", grid, 6),
        ("plus_critical_nonplanar", grid + [critical], 7),
        ("plus_one_separating", grid + [separating1], 7),
        ("plus_two_separating", grid + [separating1, separating2], 8),
        ("critical_then_separating", grid + [critical, separating1], 8),
    ]
    ea = list(map(F, [0, 0, 0, 0, 0, -1, 0, 1, 0]))
    results = []
    for name, pairs, expected in cases:
        assert len(set(tuple(x) for x, y in pairs)) == len(pairs)
        assert len(set(tuple(y) for x, y in pairs)) == len(pairs)
        rows = design(pairs)
        assert all(sum((x * y for x, y in zip(row, ea, strict=True)), F(0)) == 0 for row in rows)
        actual, pivots, reduced = rank(rows)
        assert actual == expected
        results.append(
            {
                "name": name,
                "rank": actual,
                "nullity": 9 - actual,
                "pivots": pivots,
                "rref": reduced,
                "first_and_second_rays_unique": True,
            }
        )
    out = {
        "evidence": "exact Fraction elimination; not a Lean rank proof",
        "row_convention": "flatten E row-major, row_ij=y_i*x_j",
        "cases": results,
        "conclusion": "rank8 selects unique nonzero matrix up to scale; pose still needs decomposition and cheirality",
    }
    (HERE / "domain_rank_gate_results.json").write_text(
        json.dumps(out, default=str, indent=2) + "\n"
    )
    print([(r["name"], r["rank"], r["nullity"]) for r in results])


if __name__ == "__main__":
    main()
