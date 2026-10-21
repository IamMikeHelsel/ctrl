"""Exact unchanged-center initial entry certificates; pending admission is separate."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

R = F(2221, 40000)
eps = [F(1, 1000), F(1, 100), F(1, 20)]
rows = []
for label, v, a in [
    ("old_corner", F(1, 50), F(5, 4)),
    ("widened_reject", F(3, 100), F(5, 4)),
    ("new_initial_only", F(3, 10), F(-1)),
    ("pending_escape", F(-1, 5), F(72, 625)),
    ("inventor_band_corner", F(3, 100), F(31, 25)),
]:
    c = v / 4 + a / 32
    vertices = []
    for signs in product([-1, 1], repeat=3):
        ex, ev, ea = [s * e for s, e in zip(signs, eps, strict=True)]
        x, vt, at = ex, v + ev, a + ea
        z = [x - c, x - c + vt / 4, x - c + vt / 2 + at / 16]
        vertices.append({"errors": [ex, ev, ea], "state": [x, vt, at], "z": z})
    supports = [max(abs(p["z"][i]) for p in vertices) for i in range(3)]
    direct = all(x <= R for x in supports)
    strips = abs(8 * v + a) <= F(928, 625) and abs(a) <= F(2081, 1250)
    assert direct == strips
    rows.append(
        {
            "label": label,
            "reading": [0, v, a],
            "center": c,
            "vertices": vertices,
            "facet_absolute_supports": supports,
            "robust_initial_pass": direct,
            "radius": R,
        }
    )
escape = next(r for r in rows if r["label"] == "pending_escape")["vertices"][0]
assert escape["z"][2] == -R
v, a = escape["state"][1:]
outward = v + a / 2 + 8 * (F(-121, 100) - a) / 16
assert outward == F(-163, 200)
result = {
    "cases": rows,
    "pending_escape_z3_derivative_r8_d0": outward,
    "scope": "Exact time-zero sensor-box containment. Does not assert delayed entry for any new positive case; negative pending derivative binds source command/rate.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(
    [
        (r["label"], r["robust_initial_pass"], list(map(str, r["facet_absolute_supports"])))
        for r in rows
    ]
)
