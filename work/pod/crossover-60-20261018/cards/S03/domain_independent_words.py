"""Independent Fraction replay of declared Q16 overflow and exact plant endpoints."""

import json
from fractions import Fraction as F
from pathlib import Path


def nearest_even(q):
    a, r = divmod(q.numerator, q.denominator)
    return a + int(2 * r > q.denominator or (2 * r == q.denominator and a % 2))


def wrap16(n):
    return (n + 32768) % 65536 - 32768


def energy(x, v):
    return 5 * x * x + 2 * x * v + v * v


def endpoint(x, v, u, h=F(1, 2)):
    xx, vv = x + h * v + h * h * u / 2, v + h * u
    return {"x": str(xx), "v": str(vv), "energy": str(energy(xx, vv))}


x, v, scale = F(-1, 20), F(7, 20), 65536
X, V = nearest_even(x * scale), nearest_even(v * scale)
raw = -2 * X - 3 * V
wrapped = wrap16(-2 * X - wrap16(3 * V))
correct = F(max(-scale, min(scale, raw)), scale)
wrong = F(max(-scale, min(scale, wrapped)), scale)
assert (X, V, raw, wrapped) == (-3277, 22938, -62260, 3276)
assert energy(x, v) == F(1, 10)
assert abs(correct - (-2 * x - 3 * v)) <= F(5, 2 * scale)
assert wrong - correct == 1
valid, invalid = endpoint(x, v, correct), endpoint(x, v, wrong)
assert F(valid["energy"]) <= F(1, 10) < F(invalid["energy"])
result = {
    "scope": "Independent explicit modulo16 arithmetic toy, not C signed-overflow semantics or original implementation.",
    "initial_energy": str(energy(x, v)),
    "X": X,
    "V": V,
    "correct_u": str(correct),
    "wrong_u": str(wrong),
    "correct_endpoint": valid,
    "overflow_endpoint": invalid,
    "h": "1/2",
    "physical_w": "0",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))

# Stronger interior witness: every true point in its quantization cell is initially safe.
x2, v2 = F(-1, 20), F(349, 1000)
X2, V2 = nearest_even(x2 * scale), nearest_even(v2 * scale)
raw2 = -2 * X2 - 3 * V2
wrapped2 = wrap16(-2 * X2 - wrap16(3 * V2))
assert (X2, V2, raw2, wrapped2) == (-3277, 22872, -62062, 3474)
corners = [
    energy(F(2 * X2 + sx, 2 * scale), F(2 * V2 + sv, 2 * scale)) for sx in [-1, 1] for sv in [-1, 1]
]
assert max(corners) < F(1, 10)
valid2 = endpoint(x2, v2, F(raw2, scale))
invalid2 = endpoint(x2, v2, F(wrapped2, scale))
assert F(valid2["energy"]) <= F(1, 10) < F(invalid2["energy"])
result["strict_interior"] = {
    "initial_energy": str(energy(x2, v2)),
    "cell_max_energy": str(max(corners)),
    "correct_endpoint": valid2,
    "overflow_endpoint": invalid2,
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result["strict_interior"], indent=2))
