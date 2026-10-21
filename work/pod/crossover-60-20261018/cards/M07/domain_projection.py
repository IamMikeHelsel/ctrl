"""Exact finite projection/basis checks, independent of printed determinant fixtures."""

import hashlib
import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

import domain_double as d


def determinant(a):
    a = [list(map(F, r)) for r in a]
    det = F(1)
    for k in range(len(a)):
        p = next((j for j in range(k, len(a)) if a[j][k]), None)
        if p is None:
            return F(0)
        if p != k:
            a[k], a[p] = a[p], a[k]
            det = -det
        q = a[k][k]
        det *= q
        for j in range(k + 1, len(a)):
            f = a[j][k] / q
            for l in range(k + 1, len(a)):
                a[j][l] -= f * a[k][l]
    return det


b = d.bases()
expected = {"L1": 8, "L2": 28, "L3": 56, "L4p": 35, "Y1": 35, "Y2": 160, "Y3": 350, "Y4p": 224}
assert {k: len(v) for k, v in b.items()} == expected
checks = []
for n in (1, 2, 3):
    trace = F(0)
    count = 0
    for j in range(1, 9):
        for s in combinations(range(1, 9), n):
            z = d.tensor(d.blade(j), d.blade(*s))
            p = d.projY(z)
            assert d.projY(p) == p
            assert d.e(p) == {}
            assert d.i(p) == {}
            trace += p.get(((j,), s), 0)
            count += 1
    assert trace == expected["Y" + str(n)]
    for v in b["Y" + str(n)]:
        assert d.projY(v) == v
    checks.append(
        {
            "degree": n,
            "basis_vectors_checked": count,
            "trace_equals_rank": str(trace),
            "idempotent": True,
            "wedge_kernel": True,
            "contraction_kernel": True,
        }
    )

trace4 = F(0)
for left in b["L1"]:
    for right in b["L4p"]:
        z = d.tensor(left, right)
        p = d.projY(z)
        assert d.projY(p) == p and d.e(p) == {} and d.i(p) == {}
        assert d.map_right(p, d.star) == p
        trace4 += 2 * d.sp(p, z)
assert trace4 == 224
for v in b["Y4p"]:
    assert d.projY(v) == v and d.map_right(v, d.star) == v
checks.append(
    {
        "degree": "4 self-dual",
        "basis_vectors_checked": 280,
        "trace_equals_rank": str(trace4),
        "idempotent": True,
        "wedge_kernel": True,
        "contraction_kernel": True,
        "self_dual": True,
    }
)

# Exact Gram blocks, with zero cross-block checks before multiplying determinants.
blocks = {
    "L4p": [1] * 35,
    "Y1": [1] * 28 + [7],
    "Y2": [2] * 56 + [6] * 8,
    "Y3": [3] * 70 + [5] * 28,
    "Y4p": [4] * 56,
}
grams = {}
for name, sizes in blocks.items():
    vectors = b[name]
    starts = [0]
    for size in sizes:
        starts.append(starts[-1] + size)
    gr = [[d.sp(x, y) for y in vectors] for x in vectors]
    owner = [g for g, size in enumerate(sizes) for _ in range(size)]
    assert all(
        gr[i][j] == 0 for i in range(len(gr)) for j in range(len(gr)) if owner[i] != owner[j]
    )
    ds = []
    for lo, hi in zip(starts, starts[1:], strict=False):
        ds.append(determinant([r[lo:hi] for r in gr[lo:hi]]))
    total = F(1)
    for det in ds:
        assert det > 0
        total *= det
    grams[name] = {
        "block_sizes": sizes,
        "distinct_block_determinants": sorted(set(map(str, ds))),
        "determinant": str(total),
    }
assert F(grams["L4p"]["determinant"]) == F(1, 2**35)
assert F(grams["Y1"]["determinant"]) == 2**31
assert F(grams["Y2"]["determinant"]) == 3**56 * 7**8
assert F(grams["Y3"]["determinant"]) == 2**168 * 3**28
assert F(grams["Y4p"]["determinant"]) == 2**224 * 5**56
factor = (
    F(grams["L4p"]["determinant"]) * F(grams["Y3"]["determinant"]) * F(grams["Y1"]["determinant"])
)
assert factor == 2**164 * 3**28
# Negative control: source pairing of a self-dual basis vector with itself is not coordinate1.
assert d.sp(b["L4p"][0], b["L4p"][0]) == F(1, 2)
result = {
    "scope": "Exact Fraction finite checks; not Lean and not final symbol determinant reproduction",
    "dimensions": expected,
    "projection_checks": checks,
    "gram_checks": grams,
    "target_pairing_vs_coordinates_factor": "2^164 * 3^28",
    "negative_control_L4p_self_pairing": "1/2, not coordinate coefficient1",
    "source_core_sha256": hashlib.sha256(d.CORE.read_bytes()).hexdigest(),
    "double_module_sha256": hashlib.sha256(Path(d.__file__).read_bytes()).hexdigest(),
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(
    "PASS",
    json.dumps({"projection_counts": checks, "Gram_factor": "2^164*3^28", "dimensions": expected}),
)
