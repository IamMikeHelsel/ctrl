"""Independent sparse-polynomial connection check, using only critic Clifford code."""

import json
from fractions import Fraction as F
from pathlib import Path

from critic_operator import add, cliff, exterior

# Polynomials represented by sorted tuples of variable indices, including constants ().
A = {
    (1, (0,), (2, 3)): F(1, 2),
    (0, (1,), (2, 3)): F(-1, 2),
    (3, (2,), (0, 1)): F(1, 2),
    (2, (3,), (0, 1)): F(-1, 2),
}
dA = {}
AA = {}
for (i, mon, blade), value in A.items():
    for k, j in enumerate(mon):
        form, sign = exterior((j,), (i,))
        if sign:
            add(dA, (form, mon[:k] + mon[k + 1 :], blade), sign * value)
    for (j, mon2, blade2), value2 in A.items():
        form, sign = exterior((i,), (j,))
        if sign:
            word, metric = cliff(blade, blade2)
            add(AA, (form, tuple(sorted(mon + mon2)), word), sign * metric * value * value2)
assert not AA
assert dA == {((0, 1), (), (2, 3)): 1, ((2, 3), (), (0, 1)): 1}
dF = {}
AF = {}
for (form, mon, blade), value in dA.items():
    for k, j in enumerate(mon):
        outform, sign = exterior((j,), form)
        if sign:
            add(dF, (outform, mon[:k] + mon[k + 1 :], blade), sign * value)
    for (i, mon2, blade2), value2 in A.items():
        outform, sign = exterior((i,), form)
        if not sign:
            continue
        ab, sab = cliff(blade2, blade)
        ba, sba = cliff(blade, blade2)
        outmon = tuple(sorted(mon + mon2))
        add(AF, (outform, outmon, ab), sign * sab * value * value2)
        add(AF, (outform, outmon, ba), -sign * sba * value * value2)
assert not dF and not AF
# Curvature is pair symmetric but has cyclic defect R0123-R0213+R0312 = 1.
# Since there is no soldering/torsion-free premise, this is a gauge-connection witness.
report = {
    "status": "pass",
    "curvature_terms": [str(x) for x in sorted(dA.items())],
    "A_wedge_A_terms": len(AA),
    "dF_terms": len(dF),
    "commutator_AF_terms": len(AF),
    "algebraic_defect_0123": 1,
    "scope": "Exact polynomial identity in a local trivial gauge bundle; not Levi-Civita curvature.",
    "imports": "critic_operator only; no producer routines",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
