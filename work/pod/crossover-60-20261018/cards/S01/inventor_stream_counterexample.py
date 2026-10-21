"""Source C8 witness: changing a bounded sensor stream prevents prefix gluing."""

import json
from fractions import Fraction as F
from pathlib import Path

h = F(1, 2000)
sigma = F(632, 2000)


def brake(t):
    return (F(1, 1000) + F(39, 100) * t - F(3, 5) * t * t, F(39, 100) - F(6, 5) * t, -F(6, 5))


def center(m):
    offsets = (m[0], m[0] + m[1] / 4, m[0] + m[1] / 2 + m[2] / 16)
    error = (F(101533, 100000000), F(368033, 100000000), F(1042283, 100000000))
    weight = (F(51, 50), F(101, 100), F(1))
    radius = max(
        [F(9, 200)]
        + [
            (offsets[i] - offsets[j] + error[i] + error[j]) / (weight[i] + weight[j])
            for i in range(3)
            for j in range(3)
        ]
    )
    return max(offsets[i] + error[i] - weight[i] * radius for i in range(3))


def command(c, m):
    raw = -8 * (m[0] - c) - 6 * m[1] - m[2] / 2
    return max(-2, min(2, raw)), raw


m = brake(sigma)
g1 = brake(sigma + h)
c = center(m)
u0, raw0 = command(c, m)
assert u0 == F("0.22264264")
noises = [(F(0), F(0), F(sign, 40)) for sign in [1, -1]]
readings = [tuple(s + e for s, e in zip(g1, noise, strict=True)) for noise in noises]
controls = [command(c, reading) for reading in readings]
assert all(u == raw and -2 < raw < 2 for u, raw in controls)
assert readings[0][2] - readings[1][2] == F(1, 20)
assert controls[0][0] - controls[1][0] == -F(1, 40)
rate = F(12)
assert rate * (controls[0][0] - controls[1][0]) == -F(3, 10)
assert all(abs(noise[2]) <= F(1, 20) for noise in noises)
# At t=2h both states coincide: pending and the first digital cell use the
# same m, same rate/error, and same initial state. epsilon1 first affects
# command at 2h. Exact held-flow equality is a source dependency fact, not
# an evaluated transcendental state needed for this derivative difference.
result = {
    "source_witness_first_index": 632,
    "sigma": str(sigma),
    "same_first_reading_m": [str(v) for v in m],
    "same_state_at_local_h": [str(v) for v in g1],
    "center": str(c),
    "first_digital_command": str(u0),
    "sensor_choices_at_local_sample1": [[str(v) for v in e] for e in noises],
    "readings_at_sample1": [[str(v) for v in row] for row in readings],
    "commands_dispatch2h": [str(v[0]) for v in controls],
    "command_difference": str(controls[0][0] - controls[1][0]),
    "outgoing_acceleration_derivative_difference": str(rate * (controls[0][0] - controls[1][0])),
    "same_physical_prefix_through_local_2h": True,
    "same_reading_prefix_through_local_h": False,
    "scope": "Both bounded noise choices fall under the source arbitrary-stream input boxes, with common actual C8 pending prefix and all other choices fixed. They illustrate incompatibility of horizon-specific input choices, not failure of a fixed-stream infinite construction. Differential/continuity acceptance still uses the source theorem; no new full execution has been kernel-checked here.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
