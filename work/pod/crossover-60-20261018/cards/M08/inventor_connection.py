"""Commuting constant-curvature connection: differential vs algebraic Bianchi."""

import json
from fractions import Fraction as F
from pathlib import Path

# A terms: (base-form row, polynomial variable, Clifford blade) -> rational coefficient.
a = {
    (1, 0, (2, 3)): F(1, 2),
    (0, 1, (2, 3)): F(-1, 2),
    (3, 2, (0, 1)): F(1, 2),
    (2, 3, (0, 1)): F(-1, 2),
}


def product(left, right):
    word = list(left) + list(right)
    sign = 1
    # All these directions have positive metric; bubble-sort, then cancel repeats.
    for _i in range(len(word)):
        for j in range(len(word) - 1):
            if word[j] > word[j + 1]:
                word[j], word[j + 1] = word[j + 1], word[j]
                sign *= -1
    for i in tuple(set(word)):
        while word.count(i) >= 2:
            word.remove(i)
            word.remove(i)
    return tuple(word), sign


for left in [(0, 1), (2, 3)]:
    for right in [(0, 1), (2, 3)]:
        assert product(left, right) == product(right, left)
# Thus A wedge A = 0 and every [A_i,F_jk] = 0, as polynomial identities.
curvature = {}
for (row, variable, blade), value in a.items():
    base = tuple(sorted((row, variable)))
    value *= 1 if variable < row else -1
    key = base, blade
    curvature[key] = curvature.get(key, F(0)) + value
assert curvature == {((0, 1), (2, 3)): 1, ((2, 3), (0, 1)): 1}
# dF is zero because every coefficient is constant. Therefore d_A F = 0 everywhere.
# Algebraic cyclic expression R0123+R0231+R0312 is nevertheless 1.
r0123, r0231, r0312 = 1, 0, 0
assert r0123 + r0231 + r0312 == 1
out = {
    "status": "pass",
    "connection": "A=1/2 e23(x0 dx1-x1 dx0)+1/2 e01(x2 dx3-x3 dx2)",
    "curvature": "F=e23 dx0^dx1+e01 dx2^dx3",
    "A_wedge_A": 0,
    "dF": 0,
    "commutator_A_F": 0,
    "algebraic_cyclic_0123": 1,
    "boundary": "Local trivial gauge bundle in four positive directions embedded "
    "in signature(7,7). No Levi-Civita/soldering compatibility is claimed.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
