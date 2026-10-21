"""Independent source-defined L3-to-L4+ entry and fixed minor for the sign crossing."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

import domain_double as d

B = d.bases()
v = d.blade(1)
x = d.blade(2, 3, 4)
t = B["L4p"][0]
inputs = [d.map_right(d.raise_(d.tensor(d.blade(), x)), d.cleavep), d.shift(d.tensor(d.blade(), x))]
coefficients = []
for injected in inputs:
    bp = d.map_left(injected, lambda z: d.add(d.wedge(v, z), d.interior(v, z)))
    outputs = [{}, {}, {}]
    for (a, b), c in bp.items():
        z = {(a, b): c}
        degree = len(a), len(b)
        if degree == (2, 4):
            outputs[0] = d.add(outputs[0], d.i(d.flip(d.shift(d.flip(z)))))
        if degree == (2, 2):
            outputs[1] = d.add(outputs[1], d.cleavep(d.e(z)))
        if degree == (0, 4):
            outputs[2] = d.add(outputs[2], {b: c})
    coefficients.append([2 * d.sp(y, t) for y in outputs])
assert coefficients == [[F(-4), F(0), F(1)], [F(0), F(3), F(0)]]
# A.3-A.5 fix (c1L4p,c2L4p,c3L4p)=(1,1,-1), so entry -5a+3b.
# The fixed six-dimensional complement below comes from source Y2/Y4+ projections.
rows = [("Y2", i) for i in (42, 43)] + [("Y4p", i) for i in (84, 85, 86, 87)]
cols = [B["Y3"][i] for i in (0, 1, 2, 207, 208, 209)]
minor = []
for group, index in rows:
    bp = d.map_left(B[group][index], lambda z: d.add(d.wedge(v, z), d.interior(v, z)))
    out = {}
    for (a, b), c in bp.items():
        z = {(a, b): c}
        if (len(a), len(b)) == (2, 4):
            out = d.add(out, d.projY(d.lower(z)))
        if (len(a), len(b)) == (2, 2):
            out = d.add(out, d.projY(d.flip(d.shift(z))))
    minor.append([2 * d.sp(out, z) for z in cols])


# Independent permutation definition of determinant; no PM elimination used.
def determinant(a):
    ans = F(0)
    for perm in itertools.permutations(range(len(a))):
        term = F(
            (-1) ** sum(perm[i] > perm[j] for i in range(len(a)) for j in range(i + 1, len(a)))
        )
        for i, j in enumerate(perm):
            term *= a[i][j]
        ans += term
    return ans


value = determinant(minor)
assert value == -768
result = {
    "covector": "w1",
    "input_L3": "w234",
    "target_L4p": "cleavep(w1234)",
    "entry_bilinear_coefficients": [[str(v) for v in row] for row in coefficients],
    "general_doubled_entry": "a*(-4*c1L4p+c3L4p) + 3*b*c2L4p",
    "A3_A4_A5_entry": "-5*a+3*b",
    "fixed_minor": [[str(v) for v in row] for row in minor],
    "fixed_minor_determinant": str(value),
    "seven_block_determinant": "768*(5*a-3*b)",
    "at_A3_A4_A5": [1536, 3840, -2304],
    "scope": "Literal independent source formulas for one block; PM verifies 35 copies with orientation signs. No fixture determinant used to construct entries.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
