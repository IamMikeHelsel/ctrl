"""Predeclared three-pole-pattern/two-feedforward finite screen, frozen reference."""

import json
from fractions import Fraction as F

from domain_retuned import HERE, run
from domain_transfer import mul


def main():
    results = []
    for poles in [(20, 20, 20, 40), (25, 25, 25, 25), (20, 20, 30, 30)]:
        polynomial = [F(1)]
        for pole in poles:
            polynomial = mul(polynomial, [F(pole), F(1)])
        assert polynomial[3] == 100
        kp, kd, ka = polynomial[0] / 1600, polynomial[1] / 1600, polynomial[2] / 1600 - 1
        for k, suffix in [(F(29, 480), "robust_dc"), (F(1, 16), "nominal_inverse")]:
            name = "codesign_" + "_".join(map(str, poles)) + "_" + suffix
            result = run(name, kp, kd, ka, k, snap_gain=F(1, 1600))
            result["poles_at_nominal_rate"] = list(poles)
            results.append(result)
            print(
                name,
                "error_mm",
                result["sampled_max_error_m"] * 1000,
                "jerk",
                result["sampled_peak_actual_jerk"],
                "TV",
                result["sampled_command_tv"],
            )
    (HERE / "domain_codesign_results.json").write_text(
        json.dumps(
            {
                "status": "six predeclared cases; finite-grid exploratory results only",
                "same_reference_and_zero_filter_state": True,
                "snap_gain": "1/1600",
                "cases": results,
            },
            indent=2,
        )
        + "\n"
    )


if __name__ == "__main__":
    main()
