"""Exact prospective coupled guard, preserving source center and pending command."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

R, D = F(".055525"), F(".0005")
vertices = [
    (F(".02"), F(".15")),
    (F(".16625"), F(".15")),
    (F(".02875"), F("1.25")),
    (F(".02"), F("1.25")),
]
e = [F(".001"), F(".01"), F(".05")]
initial = [[], [], []]
for mv, ma in vertices:
    assert mv >= F(".02") and F(".15") <= ma <= F("1.25") and 8 * mv + ma <= F("1.48")
    for signs in product([-1, 1], repeat=3):
        ex, ev, ea = [s * b for s, b in zip(signs, e, strict=True)]
        c = mv / 4 + ma / 32
        for i, z in enumerate(
            [ex - c, ex - c + (mv + ev) / 4, ex - c + (mv + ev) / 2 + (ma + ea) / 16]
        ):
            initial[i].append(z)
init = [(min(x), max(x)) for x in initial]
a = (F(".08488"), F("1.3"))
v = (F(".00935"), F(".1769"))
der = [[], [], []]
slope = []
for aa, vv, rr, dd in product(a, v, [F(8), F(12)], [F("-.01"), F(".01")]):
    j = rr * (F("-1.21") + dd - aa)
    for i, x in enumerate([vv, vv + aa / 4, vv + aa / 2 + j / 16]):
        der[i].append(x)
    slope.append(-8 * vv - 6 * aa - j / 2)
dr = [(min(x), max(x)) for x in der]
assert dr[0][0] > 0 and dr[1][0] > 0 and dr[2][1] < 0
assert init[0][1] + dr[0][1] * D < 0 and init[1][1] + dr[1][1] * D < 0
lower2 = init[2][0] + dr[2][0] * D
assert lower2 > -R and init[2][1] == F(".055375")
assert max(abs(min(slope)), abs(max(slope))) < 8
assert max(-init[0][0], -init[1][0], init[2][1], -lower2) == F(".055375")
area = (
    abs(
        sum(
            vertices[i][0] * vertices[(i + 1) % 4][1] - vertices[(i + 1) % 4][0] * vertices[i][1]
            for i in range(4)
        )
    )
    / 2
)
assert area == F(".08525")
out = {
    "guard": "mv>=.02; .15<=ma<=1.25; 8mv+ma<=1.48; original center frozen",
    "vertices": [[str(x) for x in z] for z in vertices],
    "initial_ranges": [[str(x) for x in z] for z in init],
    "a_enclosure": [str(x) for x in a],
    "v_enclosure": [str(x) for x in v],
    "derivative_ranges": [[str(x) for x in z] for z in dr],
    "slope_range": [str(min(slope)), str(max(slope))],
    "z2_lower_bound": str(lower2),
    "startup_abs_bound": str(F(".055375")),
    "measurement_area": str(area),
    "old_rectangle_area": str(F(".1")),
    "union_area_ratio": str(1 + area / F(".1")),
    "scope": "Exact polytope/interval vertex certificates plus hand ODE mean-value bridge; geometry area is not probability/performance. Positive polygon extends old guard by union; no hardware/existence/detector/15cm claim.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
