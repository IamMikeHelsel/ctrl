"""Exact changed-inertia negative control; normalized model, no robot execution."""

import json
from fractions import Fraction as F
from pathlib import Path

mass1, mass2 = F(1), F(101, 50)
tau1, tau2 = -F(1, 10), F(1, 5)
v1, v2 = F(1, 5), -F(1, 5)
q1, q2 = F(9, 50), -F(9, 50)
a1, a2 = tau1 / mass1, tau2 / mass2
t = F(2)
positions = (q1 + v1 * t + a1 * t * t / 2, q2 + v2 * t + a2 * t * t / 2)
velocities = (v1 + a1 * t, v2 + a2 * t)
assert a1 + a2 == -F(1, 1010)
assert sum(positions) == -F(1, 505)
assert sum(velocities) == -F(1, 505)
# Exact corrected task cancellation would exceed the unchanged second torque bound.
corrected_tau2 = mass2 * F(1, 10)
assert corrected_tau2 == F(101, 500) > F(1, 5)
# Lower both accelerations: dynamic cancellation and torque limits can coexist,
# but the original stopping time/envelope must change.
new_magnitude = F(1, 5) / mass2
new_stop_time = v1 / new_magnitude
new_stop_position = q1 + v1 * F(1, 20) + v1 * v1 / (2 * new_magnitude)
assert new_stop_time == F(101, 50)
assert new_stop_position == F(49, 125) < F(2, 5)
out = {
    "model": "M=diag(1,101/50); no gravity, velocity forces or disturbances",
    "task": "q1+q2=0",
    "same_torque_task_position_error_at_2": str(sum(positions)),
    "same_torque_task_velocity_at_2": str(sum(velocities)),
    "same_first_acceleration_corrected_tau2": str(corrected_tau2),
    "new_equal_acceleration": str(new_magnitude),
    "new_stop_time": str(new_stop_time),
    "new_worst_position_with_delay": str(new_stop_position),
    "limitation": "Exact known changed mass permits retuning. Unknown mass and physical model binding remain open.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
