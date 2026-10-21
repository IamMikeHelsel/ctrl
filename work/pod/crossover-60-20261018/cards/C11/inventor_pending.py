"""Exact robust algebra for a declared new C3 reading band, unchanged center and dynamics."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path


def Q(x):
    return F(str(x))


D, R = F(1, 2000), F(2221, 40000)
mv, ma = [Q(".029"), Q(".03")], [Q("1.23"), Q("1.24")]
errors = [[-F(1, 1000), F(1, 1000)], [-F(1, 100), F(1, 100)], [-F(1, 20), F(1, 20)]]
initial = []
for vm, am, ex, ev, ea in itertools.product(mv, ma, *errors):
    c = vm / 4 + am / 32
    x, v, a = ex, vm + ev, am + ea
    initial.append([x - c, x - c + v / 4, x - c + v / 2 + a / 16])
bounds = [[min(p[i] for p in initial), max(p[i] for p in initial)] for i in range(3)]
assert bounds == [
    [Q("-.04725"), Q("-.0446875")],
    [Q("-.04225"), Q("-.0349375")],
    [Q(".0365625"), Q(".055375")],
]
# Prior dynamical bridge required: pending target in[-1.22,-1.2] andinitial|a|<=1.3
# imply|a|<=1.3; hence|a'|<=30.24, followed by integrated lower/upper envelopes.
ab = [Q("1.18") - Q("30.24") * D, Q("1.3")]
vb = [Q(".019") - Q("1.3") * D, Q(".04") + Q("1.3") * D]
assert ab == [Q("1.16488"), Q("1.3")]
assert vb == [Q(".01835"), Q(".04065")]
derivatives, slopes = [], []
for v, a, r, d in itertools.product(vb, ab, [F(8), F(12)], [-F(1, 100), F(1, 100)]):
    jerk = r * (-F(121, 100) + d - a)
    derivatives.append([v, v + a / 4, v + a / 2 + jerk / 16])
    slopes.append(-8 * v - 6 * a - jerk / 2)
db = [[min(p[i] for p in derivatives), max(p[i] for p in derivatives)] for i in range(3)]
assert db[0][0] > 0 and db[1][0] > 0 and db[2][1] < 0
assert max(abs(s) for s in slopes) == Q("7.1732") < 8
# Opposite-side barriers: monotonicity alone needs signs to ensure|z| decreases.
assert bounds[0][1] + db[0][1] * D < 0
assert bounds[1][1] + db[1][1] * D < 0
assert bounds[2][0] + db[2][0] * D > 0
peak = max(abs(x) for row in bounds for x in row)
assert peak == Q(".055375") and R - peak == Q(".00015")
# Generic coordinate-drift inflation misses this, although actual signed flow pointsinward.
box_z2 = max(abs(m / 4 + a / 32) for m, a in itertools.product(mv, ma))
box_z2 += F(1, 1000) + F(1, 100) / 2 + F(1, 20) / 16
box_z2 += (Q(".04065") + Q("1.3") / 2 + Q("30.24") / 16) * D
assert box_z2 == Q(".056665325") > R
# Negative direction mutation: reversedpendingcommand destroysz2inwardness.
v, a, r, d = vb[1], ab[0], F(12), F(1, 100)
wrong_j = r * (F(121, 100) + d - a)
assert v + a / 2 + wrong_j / 16 > 0
result = {
    "reading_velocity": mv,
    "reading_acceleration": ma,
    "sensor_radii": [e[1] for e in errors],
    "startup_D_max": D,
    "radius": R,
    "center": "mx+mv/4+ma/32 (unchanged C3 policy)",
    "initial_facet_ranges": bounds,
    "acceleration_envelope": ab,
    "velocity_envelope": vb,
    "facet_derivative_ranges": db,
    "feedback_slope_range": [min(slopes), max(slopes)],
    "startup_cube_bound": peak,
    "margin": R - peak,
    "coarse_box_bound_z2": box_z2,
    "negative_reversed_pending_z2_derivative": v + a / 2 + wrong_j / 16,
    "scope": "Exact multi-affine vertex and integration-barrier arithmetic. ODE comparison and full delayed hold theorem remain separate bridges, not inferred from enumeration.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(
    {
        "peak": str(peak),
        "margin": str(R - peak),
        "db": [[str(x) for x in row] for row in db],
        "max_feedback_slope": str(max(abs(s) for s in slopes)),
        "box_z2": str(box_z2),
    }
)
