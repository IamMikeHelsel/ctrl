"""Independent bit-mask verification of the newly localized six/seven block."""

import json
import runpy
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path

P = Path(__file__).resolve().parent
op = runpy.run_path(str(P / "critic_operator.py"))
B = op["B"]
image = op["image"]


def pairing(x, y):
    return sum(v * y.get(k, 0) for k, v in x.items())


coefficients = []
for which in (0, 1):
    row = []
    for target in (2, 3, 4):
        c = [0] * 10
        c[which] = 1
        c[target] = 1
        row.append(2 * pairing(image("L3", {14: F(1)}, c)[0], B["L4p"][0]))
    coefficients.append(row)
assert coefficients == [[-4, 0, 1], [0, 3, 0]]
minor = []
for group, index in [("Y2", 42), ("Y2", 43)] + [("Y4p", i) for i in (84, 85, 86, 87)]:
    out = image(group, B[group][index], [1, 1, 1, 1, -1, 1, 1, 1, 1, -1])[1]
    minor.append([2 * pairing(out, B["Y3"][i]) for i in (0, 1, 2, 207, 208, 209)])
D = F(0)
for p in permutations(range(6)):
    term = F((-1) ** sum(p[i] > p[j] for i in range(6) for j in range(i + 1, 6)))
    for i, j in enumerate(p):
        term *= minor[i][j]
    D += term
assert D == -768
saved = json.loads((P / "domain_sign_block.json").read_text())
assert [[F(v) for v in r] for r in saved["fixed_minor"]] == minor
(P / "critic_sign_block.json").write_text(
    json.dumps(
        {
            "bilinear_entry_coefficients": coefficients,
            "minor": minor,
            "minor_determinant": D,
            "scope": "Independent bit-mask operators; shared declared provisional basis list. Confirms local -5a+3b entry and fixed -768minor, not a source typo claim.",
        },
        default=str,
        indent=2,
    )
    + "\n"
)
print("Local bilinear entry and six-dimensional minor independently verified.")
