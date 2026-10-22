"""Exact rational delayed-braking experiment. AI-assisted, 2026-10-21.

One-dimensional point mass, stationary wall, nonnegative forward speed.
State bounds are supplied at observation time. Delay includes observation age,
decision, transport and actuator reaction. Forward acceleration is bounded by A
during that entire delay. Brake deceleration is at least b until rest, then held.
No sensor calibration, actuator assurance, floating-point refinement or physical
safety claim is made. The Lean companion checks polynomial envelopes only.
"""

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path


@dataclass(frozen=True)
class Contract:
    speed: F
    speed_error: F
    position_error: F
    delay: F
    acceleration: F
    brake: F

    def __post_init__(self):
        values = tuple(vars(self).values())
        if any(type(value) is not F for value in values):
            raise TypeError("Use exact Fraction inputs, not floats or booleans")
        if min(values) < 0 or self.brake == 0:
            raise ValueError("Nonnegative inputs and strictly positive braking required")

    @property
    def upper_speed(self) -> F:
        return self.speed + self.speed_error

    @property
    def required_clearance(self) -> F:
        u, tau, a, b = self.upper_speed, self.delay, self.acceleration, self.brake
        return self.position_error + u * tau + a * tau**2 / 2 + (u + a * tau) ** 2 / (2 * b)

    @property
    def nominal_clearance(self) -> F:
        return self.speed**2 / (2 * self.brake)

    def admits(self, clearance: F) -> bool:
        if type(clearance) is not F:
            raise TypeError("Use exact Fraction clearance")
        return clearance >= self.required_clearance


def trajectory(contract: Contract, time: F) -> tuple[F, F]:
    """Worst-case piecewise constant-acceleration trajectory, stopped at rest."""
    if type(time) is not F or time < 0:
        raise ValueError("Nonnegative exact Fraction time required")
    u, tau, a, b = (
        contract.upper_speed,
        contract.delay,
        contract.acceleration,
        contract.brake,
    )
    if time <= tau:
        return contract.position_error + u * time + a * time**2 / 2, u + a * time
    start_position = contract.position_error + u * tau + a * tau**2 / 2
    start_speed = u + a * tau
    s = min(time - tau, start_speed / b)
    return start_position + start_speed * s - b * s**2 / 2, start_speed - b * s


def benchmark() -> dict:
    """Explicit factorial grid, not a random sample or an empirical risk estimate.

    Both decision rules are assessed against the same worst-case model. 'False
    admission' means there exists this admissible trajectory crossing the wall.
    Equality permits touching the boundary; it is not strict collision avoidance.
    """
    axes = {
        "speed": [F(1, 2), F(1), F(2)],
        "speed_error": [F(0), F(1, 10)],
        "position_error": [F(0), F(1, 50)],
        "delay": [F(0), F(1, 20), F(1, 10), F(1, 5)],
        "acceleration": [F(0), F(1), F(2)],
        "brake": [F(1), F(2), F(4)],
    }
    policies = {key: {"admitted": 0, "false_admissions": 0} for key in ("nominal", "bounded")}
    cases = 0
    for values in product(*axes.values()):
        c = Contract(*values)
        # Fixed physical clearances, independent of either decision threshold.
        for clearance in (F(i, 20) for i in range(1, 81)):
            stop_time = c.delay + (c.upper_speed + c.acceleration * c.delay) / c.brake
            end_position, _ = trajectory(c, stop_time)
            for name, accepted in (
                ("nominal", clearance >= c.nominal_clearance),
                ("bounded", c.admits(clearance)),
            ):
                policies[name]["admitted"] += int(accepted)
                policies[name]["false_admissions"] += int(accepted and end_position > clearance)
            cases += 1
    example = Contract(F(1), F(1, 10), F(1, 50), F(1, 5), F(1), F(2))
    return {
        "schema_version": 1,
        "evidence": "exact-rational finite grid under a specified one-dimensional model",
        "novelty": "known stopping-distance algebra; proposed systems composition",
        "axes": {key: [str(v) for v in values] for key, values in axes.items()},
        "clearance_grid": {"first": "1/20", "last": "4", "step": "1/20"},
        "cases": cases,
        "policies": policies,
        "example": {
            "inputs": {key: str(value) for key, value in vars(example).items()},
            "wall_clearance": "1/2",
            "nominal_required": str(example.nominal_clearance),
            "bounded_required": str(example.required_clearance),
            "naive_admits": example.nominal_clearance <= F(1, 2),
            "bounded_admits": example.admits(F(1, 2)),
        },
        "limitations": [
            "No hardware, friction estimation, moving obstacles, turning or multibody contact",
            "Input bounds are assumed valid and require separate calibration/assurance",
            "Exact arithmetic is not a formal refinement proof of this Python implementation",
            "Zero grid violations do not establish out-of-model safety or a statistical risk rate",
            "Rejected states are not repaired; actual backup availability is a separate obligation",
        ],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(benchmark(), indent=2) + "\n")
    print(args.output)
