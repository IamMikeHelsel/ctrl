"""Declared changed-task diagnostic for geometric tracking margin."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
rho, epsilon = F(4, 5), F(1, 10)
task_level = rho * rho
task_tolerance = 2 * rho * epsilon + epsilon * epsilon
assert task_level == F(16, 25)
assert task_tolerance == F(17, 100)
assert rho + epsilon == F(9, 10) < 1
assert epsilon < F(4, 5)
# Sharp outward radial error on the leftmost point.
reference = [-rho, F(0)]
physical = [-rho - epsilon, F(0)]
assert sum(x * x for x in physical) - task_level == task_tolerance
assert physical != reference
assert sum((x - y) ** 2 for x, y in zip(reference, physical, strict=True)) == epsilon**2
# Nominal derivative bounds scale with radius under unchanged T12 timing.
nominal_speed = rho * F(5, 8)
nominal_acceleration = rho * F(155, 192)
assert nominal_speed == F(1, 2)
assert nominal_acceleration == F(31, 48)
result = {
    "scope": "Changed task level from1to16/25, diagnostic family only",
    "rho": rho,
    "position_error_ball_radius": epsilon,
    "reference_task_level": task_level,
    "required_symmetric_task_tolerance_sufficient": task_tolerance,
    "actual_task_interval": [(rho - epsilon) ** 2, (rho + epsilon) ** 2],
    "joint_absolute_bound": rho + epsilon,
    "obstacle_q1_upper_on_left_branch": epsilon,
    "exact_task_equality_counterexample": {
        "reference": reference,
        "physical": physical,
        "task_error": task_tolerance,
    },
    "nominal_T12_speed_bound": nominal_speed,
    "nominal_T12_acceleration_bound": nominal_acceleration,
    "conditional_velocity_tracking_margin_to_unit_limit": 1 - nominal_speed,
    "conditional_acceleration_tracking_margin_to_unit_limit": 1 - nominal_acceleration,
    "missing_contract": "Position error alone does not bound velocity or acceleration error;"
    " physical tracking and actuator dynamics still required",
    "preserved_constraints": "jointbox[-1,1],obstacleq1<=4/5",
    "not_claimed": "This is not robustness of original exacttaskf1; no silent shrinkingofitsfiber",
}
(HERE / "inventor_scaled.json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print(json.dumps(result, default=str, indent=2))
