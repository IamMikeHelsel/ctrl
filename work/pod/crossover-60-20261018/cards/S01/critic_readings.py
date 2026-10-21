"""Independent rational check of actual C8 witness sensor-stream fork."""

import json
from fractions import Fraction as F
from pathlib import Path

here = Path(__file__).parent
source = json.loads((here / "inventor_stream_counterexample.json").read_text())
m = list(map(F, source["same_first_reading_m"]))
g = list(map(F, source["same_state_at_local_h"]))
sigma = F(79, 250)
for state, t in [(m, sigma), (g, sigma + F(1, 2000))]:
    assert state == [
        F(1, 1000) + F(39, 100) * t - F(3, 5) * t * t,
        F(39, 100) - F(6, 5) * t,
        -F(6, 5),
    ]
a = [m[0], m[0] + m[1] / 4, m[0] + m[1] / 2 + m[2] / 16]
e = list(map(F, ["101533/100000000", "368033/100000000", "1042283/100000000"]))
w = list(map(F, ["51/50", "101/100", "1"]))
radius = max(
    [F(9, 200)] + [(a[i] - a[j] + e[i] + e[j]) / (w[i] + w[j]) for i in range(3) for j in range(3)]
)
low = max(a[i] + e[i] - w[i] * radius for i in range(3))
high = min(a[i] - e[i] + w[i] * radius for i in range(3))
assert low <= high and low == F(source["center"])


def command(reading):
    return max(F(-2), min(F(2), -8 * (reading[0] - low) - 6 * reading[1] - reading[2] / 2))


assert command(m) == F(source["first_digital_command"])
controls = []
for noise, reading in zip(
    source["sensor_choices_at_local_sample1"], source["readings_at_sample1"], strict=True
):
    actual = [g[i] + F(noise[i]) for i in range(3)]
    assert actual == list(map(F, reading))
    assert all(
        abs(F(noise[i])) <= limit for i, limit in enumerate([F(1, 1000), F(1, 100), F(1, 20)])
    )
    controls.append(command(actual))
assert controls == list(map(F, source["commands_dispatch2h"]))
assert controls[0] - controls[1] == -F(1, 40)
assert 12 * (controls[0] - controls[1]) == -F(3, 10)
(here / "critic_readings.json").write_text(
    json.dumps(
        {
            "exact_rational_checks": "passed",
            "center": str(low),
            "radius": str(radius),
            "commands": [str(v) for v in controls],
            "jerk_difference": str(12 * (controls[0] - controls[1])),
            "scope": "Source-bound local fork at fixed actual C8 pending prefix; equality of earlier physical states does not imply equality of generated readings. Full ODE admissibility inherited from original theorem, not re-proved by arithmetic.",
        },
        indent=2,
    )
    + "\n"
)
print("Independent actual-witness sensor fork checks passed")
