"""Dropping terminal jerk changes the necessary support decision, not task feasibility."""

import json
from fractions import Fraction as F
from pathlib import Path

T, J, S, a, v = F(7, 8), F(10), F(400), F(51, 20), F(2601, 8000)
alpha = (T + a / J + 2 * J / S) / 2
free = (
    -alpha * a
    + J * (alpha**2 - T * alpha + T**2 / 2)
    - 2 * alpha * J**2 / S
    + F(4, 3) * J**3 / S**2
)
assert alpha == F(59, 100)
assert free == F(8531, 24000) and free - v == F(91, 3000)
result = {
    "T": str(T),
    "terminal_jerk_free_support_upper": str(free),
    "required_moment": str(v),
    "proper_j_zero_support_upper": "20511/64000",
    "scope": "Weaker necessary relaxation passes; no feasibility assertion.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(result)
