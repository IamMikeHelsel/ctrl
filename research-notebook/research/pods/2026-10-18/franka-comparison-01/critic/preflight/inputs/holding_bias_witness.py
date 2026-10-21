"""Exact equilibrium of the unchanged scalar holding law, not a handoff path."""
from fractions import Fraction as Q
import json

center = Q(1, 10)
error = (-Q(1, 1000), -Q(1, 100), -Q(1, 20))
target_error = Q(1, 100)
offset = -error[0] - Q(3, 4)*error[1] - error[2]/16 + target_error/8
state = (center + offset, Q(0), Q(0))
measurement = tuple(s + e for s, e in zip(state, error))
raw_command = -8*(measurement[0] - center) - 6*measurement[1] - measurement[2]/2
assert abs(raw_command) < 2  # clipping is inactive
assert raw_command + target_error == state[2] == 0
assert offset == Q(103, 8000)
for rate in (Q(8), Q(10), Q(12)):
    assert rate*(raw_command + target_error - state[2]) == 0
print(json.dumps({
    "scope": "Permitted equilibrium of the fixed-reference holding law; no admission reachability claim",
    "center_m": str(center),
    "equilibrium_offset_m": str(offset),
    "equilibrium_offset_mm": str(offset * 1000),
    "sensor_errors": [str(e) for e in error],
    "target_error_m_per_s2": str(target_error),
    "command_m_per_s2": str(raw_command),
    "actual_velocity": "0",
    "actual_acceleration": "0"
}, indent=2))
