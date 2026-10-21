"""Independent robust center reconstruction and source-policy distinction."""

import itertools
import json
from fractions import Fraction as Q
from pathlib import Path

P = Path(__file__).resolve().parent
m = (Q(7, 50), Q(-1, 100), Q(-117, 100))
R = Q(2221, 40000)
D = Q(1, 2000)
error = (Q(1, 1000) + Q(613, 20000) * D, Q(1, 100) + Q(13, 10) * D, Q(1, 20) + Q(756, 25) * D)
cloud = []
for signs in itertools.product((-1, 1), repeat=3):
    x, v, a = (z + s * e for z, s, e in zip(m, signs, error, strict=True))
    cloud.extend((x, x + v / 4, x + v / 2 + a / 16))
lo, hi = min(cloud), max(cloud)
center = (lo + hi) / 2
radius = (hi - lo) / 2
forward = hi - R + Q(1, 1000)
assert (lo, hi, center, radius, forward) == tuple(
    map(Q, [".051464675", ".141177825", ".09632125", ".044856575", ".086652825"])
)
assert max(abs(x - center) for x in cloud) == radius
assert all(abs(x - forward) <= R for x in cloud)
assert forward + R == Q(".142177825")
assert any(abs(x - (hi - R - Q(1, 10**6))) > R for x in cloud)
old = m[0] + m[1] / 4 + m[2] / 32
old_command = -8 * (m[0] - old) - 6 * m[1] - m[2] / 2
new_command = -8 * (m[0] - forward) - 6 * m[1] - m[2] / 2
assert old_command != new_command and new_command - old_command == 8 * (forward - old)
# Immutable-policy mutation: a geometry certificate does not change source center definition.
assert forward != old
# Different maximizing corners still require both separate extrema.
assert max(x + y for x, y in itertools.product((-1, 1), repeat=2)) == 2
assert max(x - y for x, y in itertools.product((-1, 1), repeat=2)) == 2
assert not any(x + y == 2 and x - y == 2 for x, y in itertools.product((-1, 1), repeat=2))
assert any(x + y > 1 for x, y in itertools.product((-1, 1), repeat=2))
producer = json.loads((P / "pm_center.json").read_text())
assert Q(producer["U"]) == hi and Q(producer["L"]) == lo
out = {
    "source_envelope_corner_count": 8,
    "three_facets_each": 24,
    "L": str(lo),
    "U": str(hi),
    "minimax_center": str(center),
    "minimax_radius": str(radius),
    "prospective_forward_center": str(forward),
    "prospective_upper": str(forward + R),
    "old_center": str(old),
    "old_command": str(old_command),
    "new_command": str(new_command),
    "policy_equality_negative": "rejected: changes held target by8 delta-center",
    "joint_maximizer_negative": "disjoint maximizers do not justify dropping universal facet constraints",
    "scope": "Exact startup box containment only; changed-center feedback needs its own Execution binding.",
}
(P / "critic_center.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
