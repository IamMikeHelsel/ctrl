"""Two exact entries only; tests coefficient scaling versus matrix scaling."""

import json
from fractions import Fraction as F
from pathlib import Path

import domain_double as d

b = d.bases()
v = d.blade(1)


def symbol(x):
    return d.map_left(x, lambda a: d.add(d.wedge(v, a), d.interior(v, a)))


def input_l3(x, c):
    return d.add(
        d.scale(c, d.map_right(d.raise_(d.tensor(d.blade(), x)), d.cleavep)),
        d.scale(c, d.shift(d.tensor(d.blade(), x))),
    )


def output_l2(bp, c):
    result = {}
    for (a, z), coef in bp.items():
        term = {(a, z): coef}
        if (len(a), len(z)) == (2, 4):
            out = d.i(term)
        elif (len(a), len(z)) == (2, 2):
            out = d.e(d.lower(term))
        elif (len(a), len(z)) == (0, 2):
            out = d.scale(coef, {z: F(1)})
        else:
            out = {}
        result = d.add(result, d.scale(c, out))
    return result


def output_y1(bp):
    return d.projY(d.lower({(a, z): c for (a, z), c in bp.items() if (len(a), len(z)) == (2, 2)}))


l3 = []
for j, x in enumerate(b["L3"]):
    y = output_l2(symbol(input_l3(x, F(1))), F(1))
    for k, z in enumerate(b["L2"]):
        a = d.sp(y, z)
        if a:
            vals = [d.sp(output_l2(symbol(input_l3(x, F(c))), F(c)), z) for c in (1, 2, 3)]
            assert vals == [a, 4 * a, 9 * a]
            l3 = [j, k, list(map(str, vals))]
            break
    if l3:
        break
l1 = []
for j, x in enumerate(b["L1"]):
    y = output_y1(symbol(d.raise_(d.tensor(d.blade(), x))))
    for k, z in enumerate(b["Y1"]):
        a = d.sp(y, z)
        if a:
            l1 = [j, k, str(a)]
            break
    if l1:
        break
assert l3 and l1
out = {
    "covector": [1],
    "L3_to_L2_entry_scalars1_2_3": l3,
    "unscaled_L1_to_Y1_entry": l1,
    "indices": "zero based in domain_double bases; coefficients all set to common scalar",
    "scope": "Two literal source entry calculations, not full determinant homogeneity certificate",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
