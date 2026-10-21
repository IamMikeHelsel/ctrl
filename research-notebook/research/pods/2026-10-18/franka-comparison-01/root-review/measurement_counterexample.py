"""Exact measurement-conversion counterexample; no robot or plant simulation."""
from fractions import Fraction as Q
import json

period = Q(1, 1000)
velocity_error = Q(1, 100)
acceleration_allowance = Q(1, 20)
true_velocity_previous = true_velocity_now = Q(0)
read_previous = true_velocity_previous - velocity_error
read_now = true_velocity_now + velocity_error
assert abs(read_previous - true_velocity_previous) <= velocity_error
assert abs(read_now - true_velocity_now) <= velocity_error
derived_acceleration = (read_now - read_previous) / period
assert derived_acceleration == 20
assert abs(derived_acceleration) > acceleration_allowance
print(json.dumps({
    "scope": "Exact scalar sensor-box counterexample, not hardware noise data",
    "period_s": str(period),
    "velocity_error_m_per_s": str(velocity_error),
    "true_acceleration_m_per_s2": "0",
    "derived_acceleration_m_per_s2": str(derived_acceleration),
    "required_acceleration_error_m_per_s2": str(acceleration_allowance),
    "allowance_multiple": str(derived_acceleration / acceleration_allowance)
}, indent=2))
