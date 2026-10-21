"""Independent sparse differential jet and exact eight-bracket audit."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

from critic_operator import ALL, PHI1, PHI2, SIG, combine, star, tensor, wedge_bracket

R = tensor({(0, j, 0, j): SIG[j] for j in ALL if j})
D = {(0,) + key: value for key, value in R.items()}
# The jet is nonzero only in derivative direction 0.
for m, i, j, k, l in product(ALL, repeat=5):
    a = D.get((m, i, j, k, l), 0)
    assert a + D.get((i, j, m, k, l), 0) + D.get((j, m, i, k, l), 0) == 0
    assert a + D.get((m, i, k, l, j), 0) + D.get((m, i, l, j, k), 0) == 0
DR = {
    (m, i, l): sum(SIG[j] * D.get((m, j, i, j, l), 0) for j in ALL)
    for m, i, l in product(ALL, repeat=3)
}
div = [sum(SIG[i] * DR[i, i, l] for i in ALL) for l in ALL]
grad = [sum(SIG[i] * DR[m, i, i] for i in ALL) for m in ALL]
assert div == [13] + [0] * 13 and grad == [26] + [0] * 13

rho = {((0, 1), (0, 1)): F(1)}
expected = {((i,), (i,)): F(2) for i in ALL if i not in (0, 1)}
rows = {}
for first, inner, outer in product("CJ", repeat=3):
    a = wedge_bracket(PHI1, star(rho), -1 if first == "C" else 1)
    q = star(wedge_bracket(PHI2, star(rho), -1 if inner == "C" else 1))
    b = star(wedge_bracket(PHI1, q, -1 if outer == "C" else 1))
    # Keep real and imaginary parts separately as rational sparse dictionaries.
    real, imag = {}, {}
    if first == "C":
        real = combine(real, a)
    else:
        imag = combine(imag, a)
    phase = (inner == "J") + (outer == "J")
    if phase == 0:
        real = combine(real, b, F(-1, 2))
    elif phase == 1:
        imag = combine(imag, b, F(-1, 2))
    else:
        real = combine(real, b, F(1, 2))
    real, imag = star(real), star(imag)
    rows[first + inner + outer] = {
        "real_terms": len(real),
        "imag_terms": len(imag),
        "matches": real == expected and not imag,
    }
    if first + inner + outer == "CCC":
        assert real and not (set(real) & set(expected))
assert [k for k, v in rows.items() if v["matches"]] == ["CJJ"]
report = {
    "status": "pass",
    "jet_nonzero_components": len(D),
    "divRic": div,
    "scalar_gradient": grad,
    "jet_scope": "Admitted pointwise differential-curvature jet, no constructed global metric",
    "bracket_choices": rows,
    "normalization_selection": "Divergence(2Ric-beta*scalar*g)=26*(1-beta) along this jet",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2, default=str) + "\n")
print(json.dumps(report, indent=2, default=str))
