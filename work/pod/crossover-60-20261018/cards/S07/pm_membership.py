"""Exact one-dimensional membership certificates for the source-bound capsule."""

import json
from fractions import Fraction as F
from pathlib import Path

P = [
    [F(38, 5), F(257, 25), F(5)],
    [F(257, 25), F(1319, 50), F(769, 50)],
    [F(5), F(769, 50), F(278, 25)],
]
g = (F(1), F(-1), F(1))
D = F(1, 25)


def bilinear(x, y):
    return sum(x[i] * P[i][j] * y[j] for i in range(3) for j in range(3))


def certificate(z):
    optimum = bilinear(g, z) / bilinear(g, g)
    d = max(-D, min(D, optimum))
    core = tuple(x - d * k for x, k in zip(z, g, strict=True))
    residual = bilinear(core, core)
    return {
        "state": list(map(str, z)),
        "delta": str(d),
        "core": list(map(str, core)),
        "core_energy": str(residual),
        "state_energy": str(bilinear(z, z)),
        "member": residual <= 12,
    }


cases = {
    "origin": (F(0), F(0), F(0)),
    "active_core": (F(29, 20), F(-27, 20), F(37, 20)),
    "active_extra": (F(149, 100), F(-139, 100), F(189, 100)),
    "beyond_largest_P_dilation": tuple(F(18217, 10000) * x for x in g),
    "too_wide_old_capsule": (F(81, 40), F(-888573, 710015) - F(1, 8), F(622402, 710015) + F(1, 8)),
    "outside_travel": (F(201, 100), F(-9400167, 7100150), F(3292179, 3550075)),
}
results = {name: certificate(z) for name, z in cases.items()}
assert all(results[k]["member"] for k in list(cases)[:4])
assert not any(results[k]["member"] for k in list(cases)[4:])
assert F(results["active_extra"]["state_energy"]) > 12
assert F(results["beyond_largest_P_dilation"]["state_energy"]) > F(44527328, 3550075)
# Exact first-order optimality of the constrained quadratic; no solver status.
for item in results.values():
    z = tuple(map(F, item["state"]))
    d = F(item["delta"])
    slope = 2 * (bilinear(g, g) * d - bilinear(g, z))
    assert (d == -D and slope >= 0) or (d == D and slope <= 0) or slope == 0
Path(__file__).with_suffix(".json").write_text(
    json.dumps(
        {
            "scope": "exact membership and quadratic optimality only; no floating-point or runtime adapter",
            "cases": results,
        },
        indent=2,
    )
    + "\n"
)
print("6 exact membership certificates and constrained-optimality checks pass")
