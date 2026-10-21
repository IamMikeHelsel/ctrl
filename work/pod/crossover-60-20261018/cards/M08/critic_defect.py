"""Independent exact defect-basis audit with tuple Clifford words."""

import json
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement
from pathlib import Path

from critic_operator import ALL, SIG, add, cliff, tensor

count = nonzero = 0
for p, q in combinations_with_replacement(list(combinations(ALL, 2)), 2):
    R = tensor({p + q: 1})
    raw = {}
    for ij, kl in {(p, q), (q, p)}:
        s = SIG[ij[0]] * SIG[ij[1]] * SIG[kl[0]] * SIG[kl[1]]
        a, sa = cliff(ij, kl)
        b, sb = cliff(kl, ij)
        add(raw, a, s * sa)
        add(raw, b, s * sb)
    Q4 = {key: value for key, value in raw.items() if len(key) == 4}
    expected = {}
    support = tuple(sorted(set(p + q)))
    if len(support) == 4:
        a, b, c, d = support
        defect = R.get((a, b, c, d), 0) - R.get((a, c, b, d), 0) + R.get((a, d, b, c), 0)
        expected[support] = 4 * SIG[a] * SIG[b] * SIG[c] * SIG[d] * defect
    assert Q4 == expected
    scalar = sum(SIG[i] * SIG[j] * R.get((j, i, j, i), 0) for i in ALL for j in ALL)
    assert raw.get((), 0) == -scalar
    assert all(len(blade) in (0, 4) for blade in raw)
    norm = F(0)
    for i in ALL:
        row = {}
        for blade, value in Q4.items():
            ab, sa = cliff((i,), blade)
            ba, sb = cliff(blade, (i,))
            add(row, ab, F(sa, 2) * value)
            add(row, ba, F(sb, 2) * value)
        assert all(len(blade) == 5 for blade in row)
        norm += sum(value**2 for value in row.values())
    assert norm == 10 * sum(value**2 for value in Q4.values())
    count += 1
    nonzero += bool(Q4)
assert (count, nonzero) == (4186, 3003)
# Each disjoint quadruple has three distinct coordinates and one nonzero linear equation.
assert len(list(combinations(ALL, 4))) == 1001
assert 4186 - 1001 == 3185
# An invariant indefinite squared norm cannot replace componentwise vanishing:
# Q=e0123+e0127 has metric norm +1-1=0 but Q != 0.
metric_norm = SIG[0] * SIG[1] * SIG[2] * SIG[3] + SIG[0] * SIG[1] * SIG[2] * SIG[7]
assert metric_norm == 0
report = {
    "status": "pass",
    "basis_count": count,
    "defect_basis_count": nonzero,
    "defect_rank_disjoint_blocks": 1001,
    "kernel_dimension": 3185,
    "coordinate_norm_factor": 10,
    "null_indefinite_norm_counterexample": "e0123+e0127",
    "scope": "Exact finite rational basis audit plus stated linearity; not kernel proof or invariant positive norm",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
