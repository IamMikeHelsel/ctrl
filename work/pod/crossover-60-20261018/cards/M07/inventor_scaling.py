"""Reassemble doubled coefficients and independently check entries and determinants."""

import hashlib
import json
import time
from fractions import Fraction as F
from pathlib import Path

import pm_symbol
from inventor_gram import determinant

HERE = Path(__file__).resolve().parent


def parity(indices):
    return (-1) ** sum(x > y for i, x in enumerate(indices) for y in indices[i + 1 :])


def block_det(rows):
    size = len(rows)
    adjacency = [set() for _ in range(2 * size)]
    for i, row in enumerate(rows):
        for j, value in row.items():
            if value:
                adjacency[i].add(size + j)
                adjacency[size + j].add(i)
    remaining = set(range(2 * size))
    groups = []
    while remaining:
        component = set()
        pending = [min(remaining)]
        while pending:
            node = pending.pop()
            if node not in component:
                component.add(node)
                pending.extend(adjacency[node] - component)
        remaining -= component
        rr = sorted(i for i in component if i < size)
        cc = sorted(i - size for i in component if i >= size)
        groups.append((rr, cc))
    value = F(1)
    for rr, cc in groups:
        if len(rr) != len(cc):
            return F(0)
        value *= determinant([[rows[i].get(j, 0) for j in cc] for i in rr])
    return (
        value
        * parity([i for rr, _ in groups for i in rr])
        * parity([j for _, cc in groups for j in cc])
    )


def main():
    results = []
    fixture_file = Path(
        "/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/gu-source-exploration-20261018/software/thesis-appendix/determinant-fixtures.json"
    )
    fixtures = json.loads(fixture_file.read_text())["fixtures"]
    for number in range(1, 7):
        started = time.monotonic()
        path = HERE / f"pm_matrix_A_{number}.json"
        stored = json.loads(path.read_text())
        base = [{int(j): F(v) for j, v in row} for row in stored["rows"]]
        scaled = pm_symbol.matrix([2 * c for c in stored["coefficients"]])
        counts = {0: 0, 1: 0, 2: 0}
        for i, row in enumerate(scaled):
            for j, actual in enumerate(row):
                exponent = int(8 <= i < 64) + int(j < 413)
                assert actual == base[i].get(j, 0) * 2**exponent
                if actual:
                    counts[exponent] += 1
        sparse_scaled = [{j: v for j, v in enumerate(row) if v} for row in scaled]
        old_det, new_det = block_det(base), block_det(sparse_scaled)
        fixture = fixtures[number - 1]
        expected_det = fixture["determinant_sign"]
        for prime, exponent in fixture["prime_factorization_abs"].items():
            expected_det *= int(prime) ** exponent
        assert new_det == old_det * 2**469
        if old_det:
            assert new_det != old_det * 2**448
        results.append(
            {
                "label": f"A.{number}",
                "base_matrix_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                "entry_checks": 448**2,
                "nonzero_entries_by_scaling_degree": counts,
                "original_determinant": str(old_det),
                "source_expected_determinant": str(expected_det),
                "signed_source_match": old_det == expected_det,
                "absolute_source_match": abs(old_det) == abs(expected_det),
                "source_ratio": str(old_det / expected_det) if expected_det else None,
                "doubled_coefficient_determinant": str(new_det),
                "degree469_pass": True,
                "naive_degree448_rejected": bool(old_det),
                "elapsed_seconds": time.monotonic() - started,
            }
        )
        (HERE / "inventor_scaling.json").write_text(json.dumps(results, indent=2) + "\n")
        print(
            f"A.{number}: entries and exact determinant scaling pass; {results[-1]['elapsed_seconds']:.3f}s",
            flush=True,
        )


if __name__ == "__main__":
    main()
