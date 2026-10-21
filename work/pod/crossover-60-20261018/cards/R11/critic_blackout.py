"""Declared scalar toy limits, exact fractions and controlled exponential enclosures."""

import json
import math
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def exp_negative_one():
    # Positive exp(1) series: remaining term ratio <=1/42 after first omitted41.
    lower = sum((F(1, math.factorial(i)) for i in range(41)), F(0))
    upper = lower + F(1, math.factorial(41)) / (1 - F(1, 42))
    return 1 / upper, 1 / lower


def main():
    lo, hi = exp_negative_one()
    static = (F(1, 10) * (1 - hi), F(1, 10) * (1 - lo))
    assert static[0] > F(1, 20)
    age = F(1, 50)
    acceleration = F(2)
    half = acceleration * age * age / 2
    assert half == F(1, 2500) > F(1, 10000)
    for q in (F(-1), -half, F(0), half, F(1)):
        assert max(abs(q + half), abs(q - half)) >= half
    assert max(abs(half), abs(-half)) == half
    # Two trajectories have b(0)=b'(0)=0 and b''=±A; same joint output q.
    assert acceleration * F(0) ** 2 / 2 == 0 and acceleration * F(0) == 0
    # Stale angle with exact constant-rate feedforward leaves beta*age asymptotic bias.
    stale = (age * (1 - hi), age * (1 - lo))
    assert stale[0] > F(1, 100)
    # Fresh inverse compensation with r=5, nominal=10 and beta=1 has bias.1.
    assert (1 - F(5, 10)) / 5 == F(1, 10)
    result = {
        "toy_units": "radians,seconds; first-order angle actuator qdot=r(u-q)",
        "static_frame_ramp": {
            "r": "10",
            "beta": "1",
            "time": "1/10",
            "actual_world_error_interval": list(map(str, static)),
        },
        "stale_rate_compensated_ramp": {
            "age": str(age),
            "time": "1/10",
            "actual_world_error_interval": list(map(str, stale)),
            "asymptotic_bias": str(age),
        },
        "blackout": {
            "A": str(acceleration),
            "h": str(age),
            "sharp_minimax_endpoint_error": str(half),
            "requested_radius": "1/10000",
            "common_q_values_checked": 5,
        },
        "parameter_mismatch_asymptotic_bias": "1/10",
        "scope": "Blackout lower bound assumes same available data and independent identical actuator evolution in both worlds, no fresh world-gaze or base feedback during interval. Algebraic Lean lemmas do not prove this software/causal premise.",
    }
    (HERE / "critic_blackout.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
