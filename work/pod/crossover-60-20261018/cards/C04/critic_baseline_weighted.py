"""Independent physical-coordinate replay of unchanged-gain age refinement."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
K = F(2407079, 50250000)
weights = (F(51, 50), F(101, 100), F(1))
pending = max(
    abs(-8 * v - 6 * a - r * (-F(121, 100) + d - a) / 2)
    for r, v, a, d in product(
        (F(8), F(12)),
        (-F(1533, 50000), F(1533, 50000)),
        (-F(33, 25), F(33, 25)),
        (-F(1, 100), F(1, 100)),
    )
)
assert pending == F(97066, 12500)
command_bound = sum(8 * wi * K for wi in weights)
assert command_bound == F(606, 25) * K
cap = (F(19, 10) * F(9, 200) - F(3, 1700)) * F(4, 3)
producer = json.loads((HERE / "inventor_baseline_weighted.json").read_text())
result = []
for age in (F(7, 5000), F(3, 2000)):
    w = 2 * command_bound + F(103, 1000)
    steps = []
    for _ in range(4):
        slopes = []
        for rate, signs, residual in product((F(8), F(12)), product((-1, 1), repeat=3), (-w, w)):
            z = tuple(signs[i] * weights[i] * K for i in range(3))
            x, v, a = z[0], 4 * (z[1] - z[0]), 16 * (z[0] - 2 * z[1] + z[2])
            jerk = rate * (-8 * x - 6 * v - a / 2 + residual - a)
            slopes.append(abs(-8 * v - 6 * a - jerk / 2))
        slope = max(slopes)
        assert slope == max(F(2432, 25) * K + 4 * w, F(2012, 25) * K + 6 * w)
        w = F(103, 1000) + slope * age + max(F(0), pending - slope) * min(age, F(1, 2000))
        steps.append(str(w))
    result.append({"age": str(age), "steps": steps, "third_pass_margin": str(cap - F(steps[2]))})
for row, saved in zip(result, producer["cases"], strict=True):
    assert row["steps"] == [step["output"] for step in saved["steps"]]
assert F(result[0]["third_pass_margin"]) > 0
assert F(result[1]["third_pass_margin"]) < 0
# Independent affine lower map, including its positive fixed point.
age = F(3, 2000)
intercept = F(103, 1000) + F(2432, 25) * K * (age - F(1, 2000)) + pending * F(1, 2000)
fixed = intercept / (1 - 4 * (age - F(1, 2000)))
assert fixed > cap
assert fixed == F(producer["one_point_five_ms_obstruction"]["affine_lower_map_fixed_point"])
payload = {
    "pending_max": str(pending),
    "command_norm": str(command_bound / K),
    "cases": result,
    "one_point_five_ms_affine_floor": str(fixed),
    "scope": "Exact conditional prefix arithmetic; all history must share the original weighted box. Pending overlap is a single global interval of length<=.5ms. No invariant/execution theorem or physical unsafety claim.",
}
(HERE / "critic_baseline_weighted.json").write_text(json.dumps(payload, indent=2) + "\n")
print(json.dumps(payload, indent=2))
