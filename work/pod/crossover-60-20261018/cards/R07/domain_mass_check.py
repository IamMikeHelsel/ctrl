"""Independent rational reconstruction; imports no producer code."""

import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

base = Path(__file__).parent
producer = json.loads((base / "pm_mass_mismatch.json").read_text())
mass = F(101, 50)
q0, v0, delay, limit = F(9, 50), F(1, 5), F(1, 20), F(1, 5)
second_accel = limit / mass
first_accel = -second_accel
first_torque = first_accel
second_torque = mass * second_accel
assert abs(first_torque) <= F(1, 10) and abs(second_torque) <= limit
assert first_accel + second_accel == 0
stop = v0 / second_accel
q_at_start = q0 + v0 * delay
q_at_stop = q_at_start + v0 * stop + first_accel * stop**2 / 2
assert v0 + first_accel * stop == 0
assert stop == F(101, 50) and q_at_stop == F(49, 125)
assert q_at_stop < F(2, 5)
assert 2 * q_at_stop < F(4, 5)
# Monotonicity: q1'(s)=v0(1-s/stop) lies in[0,v0] on[0,stop].
# Thus endpoint is exact maximum; q2=-q1 and task sum is identically zero.
unchanged_task_accel = -F(1, 10) + limit / mass
old_elapsed = F(2)
old_task_position = unchanged_task_accel * old_elapsed**2 / 2
old_task_velocity = unchanged_task_accel * old_elapsed
expected = {
    "same_torque_task_position_error_at_2": str(old_task_position),
    "same_torque_task_velocity_at_2": str(old_task_velocity),
    "same_first_acceleration_corrected_tau2": str(mass / F(10)),
    "new_equal_acceleration": str(second_accel),
    "new_stop_time": str(stop),
    "new_worst_position_with_delay": str(q_at_stop),
}
assert all(producer[key] == value for key, value in expected.items())
result = {
    "independent_fields_match": expected,
    "retuned_first_torque": str(first_torque),
    "retuned_second_torque": str(second_torque),
    "braking_duration": str(stop),
    "delay": str(delay),
    "total_issue_to_stop": str(delay + stop),
    "alltime_max_q1": str(q_at_stop),
    "alltime_max_z": str(2 * q_at_stop),
    "scope": "Exact known inertia; no gravity, drag, disturbances or unknown state. ODE-to-polynomial binding hand-derived.",
    "producer_sha256": hashlib.sha256((base / "pm_mass_mismatch.py").read_bytes()).hexdigest(),
}
(base / "domain_mass_check.json").write_text(json.dumps(result, indent=2) + "\n")
print("Independent retuning reconstruction: six fields match; braking2.02s, total2.07s, maxq1=.392")
