"""Exact independent entry, pending escape, and positive-band vertex audit."""

import itertools
import json
from fractions import Fraction as Q
from pathlib import Path

P = Path(__file__).resolve().parent
R = Q(2221, 40000)
D = Q(1, 2000)
SIG = (Q(1, 1000), Q(1, 100), Q(1, 20))


def coordinates(x, v, a, c):
    return (x - c, x - c + v / 4, x - c + v / 2 + a / 16)


def initial(mv, ma):
    c = mv / 4 + ma / 32
    return [
        coordinates(ex, mv + ev, ma + ea, c)
        for ex, ev, ea in itertools.product(*[(-s, s) for s in SIG])
    ]


# Every facet support is necessary individually, regardless of simultaneous maximizers.
for mv, ma in itertools.product(
    [Q(-1, 5), Q(3, 100), Q(3, 10), Q(0)], [Q(72, 625), Q(31, 25), Q(-1), Q(5, 4)]
):
    brute = all(abs(z) <= R for row in initial(mv, ma) for z in row)
    strips = abs(8 * mv + ma) <= Q(928, 625) and abs(ma) <= Q(2081, 1250)
    assert brute == strips
# Realized pending prefix, no endpoint reset; old C3's rectangle does not admit it.
mv, ma = Q(-1, 5), Q(72, 625)
c = mv / 4 + ma / 32
x, v, a = -SIG[0], mv - SIG[1], ma - SIG[2]
z = coordinates(x, v, a, c)
assert all(abs(t) <= R for row in initial(mv, ma) for t in row)
assert z[2] == -R
b = Q(-121, 100)
dz = v + a / 2 + 8 * (b - a) / 16
assert dz == Q(-163, 200)
# exp(-8t)<=1 implies this strict rational upper bound at the full legal startup D.
escape_upper = -R - Q(1639, 2500) * D - Q(121, 200) * D * D
assert escape_upper < -R
# Exact physical initial coordinates from the unchanged full sensor box.
measurements = list(itertools.product([Q(29, 1000), Q(3, 100)], [Q(123, 100), Q(31, 25)]))
cloud = [row for mv, ma in measurements for row in initial(mv, ma)]
initial_intervals = [(min(row[i] for row in cloud), max(row[i] for row in cloud)) for i in range(3)]
assert max(abs(t) for row in cloud for t in row) == Q(443, 8000)
# These enclosing bounds follow the same |a|<=1.3 pending barrier and age integration.
av = (Q(118, 100) - Q(756, 25) * D, Q(13, 10))
vv = (Q(19, 1000) - Q(13, 10) * D, Q(4, 100) + Q(13, 10) * D)
rows = []
for v, a, r, d in itertools.product(vv, av, [Q(8), Q(12)], [-Q(1, 100), Q(1, 100)]):
    ad = r * (b + d - a)
    rows.append((v, v + a / 4, v + a / 2 + ad / 16, -8 * v - 6 * a - ad / 2))
ranges = [(min(row[i] for row in rows), max(row[i] for row in rows)) for i in range(4)]
assert ranges[0][0] > 0 and ranges[1][0] > 0 and ranges[2][1] < 0
assert initial_intervals[0][1] + D * ranges[0][1] < 0
assert initial_intervals[1][1] + D * ranges[1][1] < 0
assert initial_intervals[2][0] + D * ranges[2][0] > 0
assert ranges[3] == (Q(4687, 2500), Q(17933, 2500))
assert max(abs(t) for t in ranges[3]) < 8
# A naive independently inflated coordinate box cannot exploit the signed derivative.
naive_third = initial_intervals[2][1] + (vv[1] + Q(13, 10) / 2 + Q(756, 25) / 16) * D
assert naive_third > R
out = {
    "unchanged_center_positive_measurements": measurements,
    "sensor_vertex_count": len(cloud),
    "initial_facet_intervals": initial_intervals,
    "pending_a_interval": av,
    "pending_v_interval": vv,
    "derivative_and_feedback_ranges": ranges,
    "initial_radius_margin": R - Q(443, 8000),
    "naive_third_upper": naive_third,
    "boundary_escape": {
        "measurement": [mv, ma],
        "center": c,
        "initial_coordinates": z,
        "derivative": dz,
        "at_D_upper": escape_upper,
        "R": R,
    },
    "scope": "Exact affine/multiaffine supports. ODE barrier/integration and no-first-contact links hand-derived; no new alltime source Execution theorem.",
}
(P / "critic_exact.json").write_text(json.dumps(out, default=str, indent=2) + "\n")
print(json.dumps(out, default=str, indent=2))
