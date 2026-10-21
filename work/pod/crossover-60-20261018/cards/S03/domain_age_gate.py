"""Exact known-age initialization gate for an ADC cell and retained old hold."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path


def energy(x, v):
    return 5 * x * x + 2 * x * v + v * v


def check(X, V, tau, lower, upper):
    capture = []
    current = []
    for sx, sv in product([-1, 1], repeat=2):
        x, v = F(2 * X + sx, 20000), F(2 * V + sv, 20000)
        capture.append(energy(x, v))
        for b in [lower, upper]:
            xx, vv = x + tau * v + tau * tau * b / 2, v + tau * b
            current.append({"x": str(xx), "v": str(vv), "b": str(b), "energy": str(energy(xx, vv))})
    maximum = max(current, key=lambda r: F(r["energy"]))
    return {
        "X": X,
        "V": V,
        "age": str(tau),
        "old_acceleration_interval": [str(lower), str(upper)],
        "capture_max_energy": str(max(capture)),
        "capture_admitted": max(capture) <= F(1, 10),
        "current_max": maximum,
        "current_admitted": F(maximum["energy"]) <= F(1, 10),
        "vertices": current,
    }


cases = [
    check(0, 0, F(1, 20000), F(-4001, 4000), F(4001, 4000)),
    check(-500, 3499, F(1, 20000), F(-4001, 4000), F(4001, 4000)),
]
assert cases[0]["current_admitted"]
assert cases[1]["capture_admitted"] and not cases[1]["current_admitted"]
result = {
    "scope": "Known exact age within one previous hold, acceleration interval independently admitted. Convex-quadratic vertex sufficiency derived mathematically, not full kernel checker yet. Capture interval and acceleration treated as independent outer box; may reject correlated reachable tuples.",
    "cases": cases,
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps([{k: v for k, v in c.items() if k != "vertices"} for c in cases], indent=2))
