"""Independent exact audit of the prospective selective measurement polygon."""

import itertools
import json
from fractions import Fraction as Q
from pathlib import Path

P = Path(__file__).resolve().parent
vertices = [
    (Q(".02"), Q(".15")),
    (Q(".16625"), Q(".15")),
    (Q(".02875"), Q("1.25")),
    (Q(".02"), Q("1.25")),
]
cloud = []
for mv, ma in vertices:
    assert mv >= Q(".02") and Q(".15") <= ma <= Q("1.25") and 8 * mv + ma <= Q("1.48")
    for ex, ev, ea in itertools.product(
        [-Q(".001"), Q(".001")], [-Q(".01"), Q(".01")], [-Q(".05"), Q(".05")]
    ):
        cloud.append(
            (ex - mv / 4 - ma / 32, ex + ev / 4 - ma / 32, ex + ev / 2 + ea / 16 + mv / 4 + ma / 32)
        )
initial = [(min(z[i] for z in cloud), max(z[i] for z in cloud)) for i in range(3)]
vv = (Q(".00935"), Q(".1769"))
aa = (Q(".08488"), Q("1.3"))
rows = []
for v, a, r, d in itertools.product(vv, aa, [Q(8), Q(12)], [-Q(".01"), Q(".01")]):
    ad = r * (-Q("1.21") + d - a)
    rows.append((v, v + a / 4, v + a / 2 + ad / 16, -8 * v - 6 * a - ad / 2))
dr = [(min(row[i] for row in rows), max(row[i] for row in rows)) for i in range(4)]
D = Q(".0005")
R = Q(".055525")
assert dr[0][0] > 0 and dr[1][0] > 0 and dr[2][1] < 0
assert initial[0][1] + D * dr[0][1] == Q("-.00859905")
assert initial[1][1] + D * dr[1][1] == Q("-.00093655")
assert initial[2][0] + D * dr[2][0] == Q("-.000052825")
assert (
    max(-initial[0][0], -initial[1][0], initial[2][1], -(initial[2][0] + D * dr[2][0]))
    == Q(".055375")
    < R
)
assert dr[3] == (Q(".7848"), Q("7.2452"))
# Shoelace on the actual polygon; no uniform observation distribution is assumed.
area = (
    abs(
        sum(
            x * yy - xx * y
            for (x, y), (xx, yy) in zip(vertices, vertices[1:] + vertices[:1], strict=True)
        )
    )
    / 2
)
assert area == Q(".08525")
# The only overlap with old |mv|<=.02,|ma|<=1.25 lies on v=.02, of area zero.
for v, _a in vertices:
    assert not (abs(v) < Q(".02"))
# Forgetting the shared strip admits a forbidden independent-box corner.
mv, ma = Q(".16625"), Q("1.25")
wrong_third = Q(".009125") + mv / 4 + ma / 32
assert wrong_third > R
out = {
    "measurement_vertices": vertices,
    "sensor_corners": 32,
    "initial_intervals": initial,
    "derivative_ranges": dr,
    "third_lower_after_prefix": initial[2][0] + D * dr[2][0],
    "radius_margin": R - Q(".055375"),
    "exact_polygon_area": area,
    "extra_over_old_rectangle_area_ratio": area / Q(".1"),
    "lost_measurement_correlation_negative": wrong_third,
    "scope": "Exact convex/multiaffine supports and trapezoid area, not a probability or physical performance claim. ODE/source adapter composition remains separate.",
}
(P / "critic_polygon.json").write_text(json.dumps(out, default=str, indent=2) + "\n")
print(json.dumps(out, default=str, indent=2))
