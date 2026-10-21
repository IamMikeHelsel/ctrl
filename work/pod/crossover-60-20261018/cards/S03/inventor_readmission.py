"""Exact endpoint-to-cell margin, not a hardware ADC or intersample claim."""

import json
from fractions import Fraction as F
from pathlib import Path

D = F(1, 1250)
NOMINAL = F(119, 1200)
ERROR = F(29, 64) * D**2
YOUNG = F(1001, 1000) * NOMINAL + 1001 * ERROR
rows = []
for name, scale in [("decimal", 10000), ("Q14", 16384), ("Q16", 65536)]:
    delta = F(1, scale)
    input_error = F(5, 2) * delta
    dac_allowance = D - F(1, 4000) - input_error
    cell_lift = F(84, 25) * delta + 8 * delta**2
    assert dac_allowance > 0
    assert YOUNG + cell_lift < F(1, 10)
    rows.append(
        {
            "format": name,
            "scale": scale,
            "weighted_input_error": str(input_error),
            "remaining_DAC_allowance_if_no_other_error": str(dac_allowance),
            "endpoint_energy_bound": str(YOUNG),
            "cell_energy_bound": str(YOUNG + cell_lift),
            "cell_margin": str(F(1, 10) - YOUNG - cell_lift),
        }
    )

# Safe point is not sufficient for INITIAL whole-cell admission.
x, v = F(-1, 20), F(7, 20)


def energy(a, b):
    return 5 * a * a + 2 * a * b + b * b


assert energy(x, v) == F(1, 10)
corner_energy = energy(x - F(1, 20000), v + F(1, 20000))
assert corner_energy > F(1, 10)

result = {
    "scope": "sample endpoints only; h in [1/20,1/2]; held total error <=1/1250",
    "nominal_energy_bound": str(NOMINAL),
    "held_error_energy_bound": str(ERROR),
    "young_k": 1000,
    "formats": rows,
    "initial_safe_point_fails_decimal_cell": {
        "x": str(x),
        "v": str(v),
        "energy": str(energy(x, v)),
        "cell_corner_energy": str(corner_energy),
    },
    "limitations": [
        "Input state and ADC cell must refer to the same sample instant.",
        "Nearest rounding half-grid bound; missing or stale samples are excluded.",
        "Every held delivered error obeys the declared total budget.",
        "No fallback or hardware validity follows from this arithmetic.",
    ],
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
