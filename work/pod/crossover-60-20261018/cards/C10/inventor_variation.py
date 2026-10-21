"""Changed-task negative: net displacement is not total reference variation."""

import json
from fractions import Fraction as F
from pathlib import Path

from inventor_cancellation import outward, propagate


def main():
    center, radius = [F(0), F(0), F(0), F(1)], F(0)
    q, velocity, acceleration = F(0), F(0), F(0)
    duration, rate, kappa = F(1, 50), 8, F(5, 48)
    total_variation = F(0)
    witnesses = []
    for index, jerk in enumerate((10, -10, -10, 10, -10, 10, 10, -10)):
        direction = 1 if index < 4 else -1
        points = [F(0), duration]
        critical = -acceleration / jerk
        if 0 < critical < duration:
            points.append(critical)
        assert all(direction * (velocity + acceleration * t + jerk * t**2 / 2) >= 0 for t in points)
        new_q = q + velocity * duration + acceleration * duration**2 / 2 + jerk * duration**3 / 6
        total_variation += direction * (new_q - q)
        velocity, acceleration = (
            velocity + acceleration * duration + jerk * duration**2 / 2,
            acceleration + jerk * duration,
        )
        q = new_q
        matrix = [
            [F(0), F(1), F(0), F(0)],
            [F(0), F(0), F(1), F(0)],
            [F(-8 * rate), F(-6 * rate), F(-3 * rate, 2), (rate * kappa - 1) * jerk],
            [F(0)] * 4,
        ]
        center, radius, audit = propagate(matrix, duration, center, radius)
        if index in (3, 7):
            assert velocity == acceleration == 0
        witnesses.append(
            {
                "time": (index + 1) * duration,
                "reference_q": q,
                "reference_v": velocity,
                "reference_a": acceleration,
                "position_error_lower": outward(center[0] - radius, True),
                "position_error_upper": outward(center[0] + radius, False),
                "taylor_degree": audit["degree"],
                "tail_bound": audit["tail_bound"],
            }
        )
    assert q == 0
    assert total_variation == F(1, 3125)
    final = witnesses[-1]
    assert final["position_error_upper"] < 0 or final["position_error_lower"] > 0
    result = {
        "scope": "Changed-task diagnostic only: concatenate one original short forward move and one reverse move. Not a counterexample on the original single-move task.",
        "kappa": kappa,
        "rate": rate,
        "disturbance": 0,
        "net_reference_displacement": q,
        "total_reference_variation": total_variation,
        "initial_error": [0, 0, 0],
        "physical_state_reset": False,
        "joins_q_v_a_preserved": True,
        "witnesses": witnesses,
        "conclusion": "A zero error bound obtained by replacing total variation by absolute net displacement is false. Monotonicity or a genuine total-variation bound is required.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, default=str, indent=2) + "\n")
    print(
        "net",
        q,
        "variation",
        total_variation,
        "final",
        final["position_error_lower"],
        final["position_error_upper"],
    )


if __name__ == "__main__":
    main()
