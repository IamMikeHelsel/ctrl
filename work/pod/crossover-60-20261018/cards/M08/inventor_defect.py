"""Exact finite coordinate audit; not a kernel proof or an author-selected operator."""

import json
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement
from pathlib import Path

N = 14
SIG = [1] * 7 + [-1] * 7
PAIRS = list(combinations(range(N), 2))


def add(d, k, v):
    d[k] = d.get(k, F(0)) + v
    if not d[k]:
        del d[k]


def cp(a, b):
    # Independent ordered-word reduction: insertion, followed by e_i^2=s_i.
    word = [i for i in range(N) if a & (1 << i)]
    coeff = 1
    for j in range(N):
        if not b & (1 << j):
            continue
        coeff *= (-1) ** sum(k > j for k in word)
        if j in word:
            word.remove(j)
            coeff *= SIG[j]
        else:
            word.append(j)
            word.sort()
    return sum(1 << i for i in word), coeff


def anti(a, b):
    out = {}
    for x, c in a.items():
        for y, d in b.items():
            for left, right in [(x, y), (y, x)]:
                m, sign = cp(left, right)
                add(out, m, sign * c * d)
    return out


def make_tensor(p, q):
    out = {}
    for first, second in {(p, q), (q, p)}:
        a, b = first
        c, d = second
        for i, j, sign in [(a, b, 1), (b, a, -1)]:
            for k, l, sign2 in [(c, d, 1), (d, c, -1)]:
                out[i, j, k, l] = sign * sign2
    return out


def evaluate(r):
    raw = {}
    ricci = {}
    crows = [{} for _ in range(N)]
    for (j, i, k, l), value in r.items():
        if j == k:
            add(ricci, (i, l), SIG[j] * value)
        if k < l:
            blade = 2**k + 2**l
            left, ls = cp(2**j, blade)
            right, rs = cp(blade, 2**j)
            scale = SIG[j] * SIG[k] * SIG[l] * value
            add(crows[i], left, scale * ls)
            add(crows[i], right, -scale * rs)
    for i in range(N):
        target = {2**l: 2 * SIG[l] * ricci[i, l] for l in range(N) if ricci.get((i, l), 0)}
        assert crows[i] == target
    for (i, j, k, l), v in r.items():
        if i < j and k < l:
            b = {2**i + 2**j: F(1)}
            rho = {2**k + 2**l: F(SIG[k] * SIG[l] * v)}
            for m, coeff in anti(b, rho).items():
                add(raw, m, SIG[i] * SIG[j] * coeff)
    scalar = sum(SIG[i] * SIG[j] * r.get((j, i, j, i), 0) for i in range(N) for j in range(N))
    assert raw.get(0, 0) == -scalar
    actual4 = {m: v for m, v in raw.items() if m.bit_count() == 4}
    expected4 = {}
    for a, b, c, d in combinations(range(N), 4):
        defect = r.get((a, b, c, d), 0) - r.get((a, c, b, d), 0) + r.get((a, d, b, c), 0)
        if defect:
            expected4[2**a + 2**b + 2**c + 2**d] = 4 * SIG[a] * SIG[b] * SIG[c] * SIG[d] * defect
    assert actual4 == expected4
    assert all(m.bit_count() in (0, 4) for m in raw)
    e5 = []
    for i in range(N):
        row = {m: coeff / 2 for m, coeff in anti({2**i: F(1)}, actual4).items()}
        assert all(m.bit_count() == 5 for m in row)
        e5.append(row)
    # Euclidean coordinate sum-of-squares, NOT a Spin(7,7)-invariant positive norm.
    assert sum(v * v for row in e5 for v in row.values()) == (
        (N - 4) * sum(v * v for v in actual4.values())
    )
    assert bool(actual4) == any(bool(row) for row in e5)
    return raw, e5


basis_count = 0
nonzero_defect_count = 0
for p, q in combinations_with_replacement(PAIRS, 2):
    raw, rows = evaluate(make_tensor(p, q))
    basis_count += 1
    nonzero_defect_count += any(m.bit_count() == 4 for m in raw)
assert basis_count == 4186
assert nonzero_defect_count == 3003

# Negative control: zero Ricci, nonzero algebraic Bianchi defect.
r = make_tensor((0, 1), (2, 3))
raw, rows = evaluate(r)
assert raw == {15: 4}
assert sum(bool(row) for row in rows) == 10
assert all(rows[i] == {15 + 2**i: 4} for i in range(4, 14))
assert all(not rows[i] for i in range(4))

# Each ordered quadruple supplies one independent defect, and two kernel generators.
for a, b, c, d in combinations(range(N), 4):
    tensors = [
        make_tensor((a, b), (c, d)),
        make_tensor((a, c), (b, d)),
        make_tensor((a, d), (b, c)),
    ]
    for weights in [(1, 1, 0), (0, 1, 1)]:
        rr = {}
        for weight, tensor in zip(weights, tensors, strict=True):
            for key, value in tensor.items():
                add(rr, key, weight * value)
        out, e5 = evaluate(rr)
        assert not out and not any(e5)

out = {
    "status": "pass",
    "signature": [7, 7],
    "pair_symmetric_basis_vectors_checked": basis_count,
    "nonzero_defect_basis_vectors": nonzero_defect_count,
    "independent_quadruple_defect_coordinates": 1001,
    "bianchi_kernel_dimension_by_disjoint_coordinate_blocks": 3185,
    "tested_kernel_combinations": 2002,
    "negative_control": {
        "R0123": 1,
        "Qraw": {"e0123": 4},
        "E_grade5_rows": 10,
        "each_nonzero_coefficient": 4,
    },
    "formula": "Q4_abcd=4*s_a*s_b*s_c*s_d*(R_abcd-R_acbd+R_adbc)",
    "injectivity": "sum_i coordinateNorm(E5_i)^2 = 10 coordinateNorm(Q4)^2",
    "boundary": "Finite exact Python audit plus linearity derivation; no kernel proof; "
    "coordinateNorm is not invariant under noncompact Spin(7,7).",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
