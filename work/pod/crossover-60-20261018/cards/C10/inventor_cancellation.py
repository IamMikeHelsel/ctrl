"""Exact rational Taylor enclosure of an admitted short-move rate schedule."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path


def multiply(matrix, vector):
    return [sum(a * x for a, x in zip(row, vector, strict=True)) for row in matrix]


def propagate(matrix, duration, center, radius):
    scaled = [[duration * a for a in row] for row in matrix]
    norm = max(sum(abs(a) for a in row) for row in scaled)
    bound = max(abs(x) for x in center) + radius
    degree = 0
    while True:
        ratio = norm / (degree + 2)
        if ratio < 1:
            tail = bound * norm ** (degree + 1) / factorial(degree + 1) / (1 - ratio)
            if tail < F(1, 10**55):
                break
        degree += 1
    term = center[:]
    total = center[:]
    scalar_term = F(1)
    scalar_total = F(1)
    for k in range(1, degree + 1):
        term = [x / k for x in multiply(scaled, term)]
        total = [x + y for x, y in zip(total, term, strict=True)]
        scalar_term *= norm / k
        scalar_total += scalar_term
    out_radius = radius * scalar_total + tail
    return (
        total,
        out_radius,
        {
            "duration": duration,
            "matrix": matrix,
            "norm_scaled_infinity": norm,
            "degree": degree,
            "incoming_bound": bound,
            "incoming_radius": radius,
            "tail_bound": tail,
            "outgoing_radius": out_radius,
        },
    )


def outward(value, lower, scale=10**18):
    numerator = value.numerator * scale
    integer = numerator // value.denominator if lower else -((-numerator) // value.denominator)
    return F(integer, scale)


def enclosure(kappa, rates):
    center, radius = [F(0), F(0), F(0), F(1)], F(0)
    stages = []
    signed_integral = F(0)
    for jerk, rate in zip((10, -10, -10, 10, 0), rates, strict=True):
        forcing = (rate * kappa - 1) * jerk
        signed_integral += F(1, 50) * forcing
        matrix = [
            [F(0), F(1), F(0), F(0)],
            [F(0), F(0), F(1), F(0)],
            [F(-8 * rate), F(-6 * rate), F(-3 * rate, 2), forcing],
            [F(0)] * 4,
        ]
        center, radius, audit = propagate(matrix, F(1, 50), center, radius)
        audit.update(
            {
                "jerk": jerk,
                "rate": rate,
                "forcing": forcing,
                "position_lower": outward(center[0] - radius, True),
                "position_upper": outward(center[0] + radius, False),
            }
        )
        stages.append(audit)
    return {
        "kappa": kappa,
        "rates": rates,
        "forcing_integral_to_witness": signed_integral,
        "witness_time": F(1, 10),
        "error_position_lower": outward(center[0] - radius, True),
        "error_position_upper": outward(center[0] + radius, False),
        "stages": stages,
    }


def main():
    # Original short profile: q'''=(+10,-10,-10,+10), each1/50s, then hold.
    # Original midpoint coefficient and sigma1; w=0 is within the declared bound.
    kappa = F(5, 48)
    adversarial = enclosure(kappa, (12, 8, 8, 12, 10))
    assert adversarial["forcing_integral_to_witness"] == F(1, 6)
    assert adversarial["error_position_lower"] > F(1, 5000)
    fixed = enclosure(kappa, (10, 10, 10, 10, 10))
    assert fixed["forcing_integral_to_witness"] == 0
    assert abs(fixed["error_position_lower"]) < F(1, 5000)
    assert abs(fixed["error_position_upper"]) < F(1, 5000)
    # The original jerk history has zero zeroth and first moments.
    moments = [
        sum(
            F(sign * 10, degree + 1) * ((F(i + 1, 50)) ** (degree + 1) - F(i, 50) ** (degree + 1))
            for i, sign in enumerate((1, -1, -1, 1))
        )
        for degree in range(3)
    ]
    assert moments[:2] == [0, 0]
    assert moments[2] == F(1, 3125)
    output = {
        "contract": {
            "sigma": 1,
            "kappa": kappa,
            "disturbance": 0,
            "initial_error": [0, 0, 0],
            "original_move_end": F(2, 25),
            "original_final_position": F(1, 6250),
            "original_total_horizon": F(102, 25),
            "rate_scope": "Piecewise constant admitted rate, finite joins, no controller or reference reset; continue r10 through remaining hold.",
        },
        "jerk_moments": moments,
        "admitted_varying_rate_counterexample": adversarial,
        "fixed_rate_at_same_time_negative_control": fixed,
        "evidence": "Exact Fraction Taylor arithmetic plus analytic infinite-tail bound. Not Lean certified; witness is not a peak or whole-horizon upper bound.",
    }
    path = Path(__file__).with_suffix(".json")
    path.write_text(json.dumps(output, default=str, indent=2) + "\n")
    for name, result in (("varying", adversarial), ("fixed10", fixed)):
        print(
            name,
            "position at.1s",
            result["error_position_lower"],
            result["error_position_upper"],
            "meters",
            float(result["error_position_lower"]),
            "degrees",
            [stage["degree"] for stage in result["stages"]],
        )


if __name__ == "__main__":
    main()
