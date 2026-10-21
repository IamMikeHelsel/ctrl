"""Independent sparse Kulkarni-Nomizu right-inverse and Clifford target check."""

import json
from fractions import Fraction as F
from itertools import combinations, permutations
from pathlib import Path

from critic_operator import ALL, SIG, add, cliff, sign_order

P = Path(__file__).parent


def reconstruct(T):
    tr = sum(SIG[i] * T.get((i, i), 0) for i in ALL)
    h = {
        (i, j): (T.get((i, j), 0) - (F(tr, 13) * SIG[i] if i == j else 0)) / 24
        for i in ALL
        for j in ALL
    }
    R = {}
    for (a, b), v in h.items():
        if not v:
            continue
        for z in ALL:
            c = v * SIG[z]
            add(R, (a, z, b, z), c)
            add(R, (z, a, z, b), c)
            add(R, (a, z, z, b), -c)
            add(R, (z, a, b, z), -c)
    return R


def operator(R):
    S = {}
    C = {}
    for (i, j, k, l), v in R.items():
        if k < l:
            coeff = SIG[i] * SIG[k] * SIG[l] * v
            a, sa = cliff((i,), (k, l))
            b, sb = cliff((k, l), (i,))
            add(C, (j, a), coeff * sa)
            add(C, (j, b), -coeff * sb)
        if i < j and k < l:
            coeff = SIG[i] * SIG[j] * SIG[k] * SIG[l] * v
            a, sa = cliff((i, j), (k, l))
            b, sb = cliff((k, l), (i, j))
            add(S, a, coeff * sa)
            add(S, b, coeff * sb)
    for i in ALL:
        for a, v in S.items():
            b, sb = cliff((i,), a)
            c, sc = cliff(a, (i,))
            add(C, (i, b), v * sb / 2)
            add(C, (i, c), v * sc / 2)
    return C, S


def expected(T):
    return {(i, (j,)): SIG[j] * v for (i, j), v in T.items() if v}


for i, j in combinations(ALL, 2):
    T = {(i, j): F(1), (j, i): F(1)}
    E, S = operator(reconstruct(T))
    assert E == expected(T) and all(len(k) == 0 for k in S)
for i in ALL:
    T = {(i, i): F(1)}
    E, S = operator(reconstruct(T))
    assert E == expected(T) and all(len(k) == 0 for k in S)
producer = json.loads((P / "inventor_right_inverse.json").read_text())
T = {(0, 0): F(2), (7, 7): F(-3), (0, 7): F(5, 2), (7, 0): F(5, 2)}
R = reconstruct(T)
Q = {}
for row in producer["fully_alternating_targets"]:
    indices = tuple(row["indices"])
    q = F(row["q"])
    v = F(row["R_abcd"])
    metric = 1
    for i in indices:
        metric *= SIG[i]
    assert v == q / (12 * metric)
    for perm in permutations(indices):
        add(R, perm, sign_order(perm) * v)
    Q[indices] = q
E, S = operator(R)
assert {k: v for k, v in E.items() if len(k[1]) == 1} == expected(T)
assert {k: v for k, v in S.items() if len(k) == 4} == Q
expected5 = {}
for i in ALL:
    for blade, v in Q.items():
        if i not in blade:
            word = tuple(sorted((i,) + blade))
            add(expected5, (i, word), sign_order((i,) + blade) * v)
assert {k: v for k, v in E.items() if len(k[1]) == 5} == expected5
report = {
    "status": "pass",
    "symmetric_basis_reconstructed": 105,
    "producer_four_targets_consumed": 5,
    "mixed_target_actual_clifford_components": "exact match in grades1and5",
    "general_rank": 1106,
    "general_rank_scope": "hand right-inverse and grade-separation argument, not Lean",
    "independent_implementation": "Sparse KN assembly and own tuple Clifford; no producer imports",
}
(P / "critic_inverse.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
