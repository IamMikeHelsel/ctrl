"""Exact right-inverse checks; general rank conclusion also needs linearity reasoning."""

import json
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path

from inventor_defect import SIG, N, add, anti, cp, evaluate


def metric(i, j):
    return SIG[i] if i == j else 0


def kn(h):
    out = {}
    for i, j, k, l in product(range(N), repeat=4):
        value = (
            h.get((i, k), 0) * metric(j, l)
            + h.get((j, l), 0) * metric(i, k)
            - h.get((i, l), 0) * metric(j, k)
            - h.get((j, k), 0) * metric(i, l)
        )
        if value:
            out[i, j, k, l] = value
    return out


def components(r):
    raw, _ = evaluate(r)
    rows = [{} for _ in range(N)]
    for (j, i, k, l), value in r.items():
        if k < l:
            scale = SIG[j] * SIG[k] * SIG[l] * value
            m, sign = cp(2**j, 2**k + 2**l)
            add(rows[i], m, scale * sign)
            m, sign = cp(2**k + 2**l, 2**j)
            add(rows[i], m, -scale * sign)
    for i in range(N):
        for m, value in anti({2**i: F(1)}, raw).items():
            add(rows[i], m, value / 2)
    return rows


def right_inverse(t):
    trace = sum(SIG[i] * t.get((i, i), 0) for i in range(N))
    h = {
        (i, j): (t.get((i, j), 0) - F(trace, 13) * metric(i, j)) / 24
        for i in range(N)
        for j in range(N)
    }
    return kn(h)


def check(t):
    r = right_inverse(t)
    rows = components(r)
    expected = [{2**j: SIG[j] * t[i, j] for j in range(N) if t.get((i, j), 0)} for i in range(N)]
    assert rows == expected
    return r


# Every coordinate target of Sym^2, including all mixed-sign targets.
for i in range(N):
    check({(i, i): F(1)})
for i, j in combinations(range(N), 2):
    check({(i, j): F(1), (j, i): F(1)})

# Five representative fully alternating four-tensor inverses, one for each
# possible number of negative-sign indices, plus a combined mixed target.
four_tests = []
combined = check({(0, 0): F(2), (7, 7): F(-3), (0, 7): F(5, 2), (7, 0): F(5, 2)})
expected_q = {}
for nnegative in range(5):
    indices = tuple(range(4 - nnegative)) + tuple(range(7, 7 + nnegative))
    sign_product = 1
    for i in indices:
        sign_product *= SIG[i]
    q = F(nnegative + 1, 7)
    value = q / (12 * sign_product)
    r = {}
    for perm in permutations(indices):
        parity = sum(perm[i] > perm[j] for i in range(4) for j in range(i + 1, 4))
        r[perm] = (-1) ** parity * value
        add(combined, perm, r[perm])
    raw, rows = evaluate(r)
    mask = sum(2**i for i in indices)
    assert raw == {mask: q}
    assert all(all(m.bit_count() == 5 for m in row) for row in components(r))
    expected_q[mask] = q
    four_tests.append({"indices": indices, "q": str(q), "R_abcd": str(value)})
raw, _ = evaluate(combined)
assert {m: value for m, value in raw.items() if m.bit_count() == 4} == expected_q
combined_rows = components(combined)
for i in range(N):
    t = {(0, 0): F(2), (7, 7): F(-3), (0, 7): F(5, 2), (7, 0): F(5, 2)}
    assert {m: v for m, v in combined_rows[i].items() if m.bit_count() == 1} == {
        2**j: SIG[j] * t[i, j] for j in range(N) if t.get((i, j), 0)
    }

out = {
    "status": "pass",
    "symmetric_target_basis_count": 105,
    "fully_alternating_targets": four_tests,
    "combined_target": "pass",
    "right_inverse": "h=(T-tr_g(T)*g/13)/24; R=h wedge_KN g",
    "four_form_right_inverse": "R_abcd=q_abcd/(12*s_a*s_b*s_c*s_d), fully alternating",
    "rank_conclusion": "105+1001=1106 by general right-inverse formulas and grade separation",
    "boundary": "Exact executable checks plus general hand assembly; no kernel proof "
    "or global metric realization.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
