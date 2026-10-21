"""Exact measurement-domain tests; no numerical integration or physical excitation."""

import json
from fractions import Fraction as F
from pathlib import Path


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def normsq(a):
    return a[0] * a[0] + a[1] * a[1]


w0, d0 = (F(1, 2), F(0)), (F(1, 2), F(0))
w1, d1 = (F(1, 2), F(1)), (F(1, 2), -F(1))
assert add(w0, d0) == add(w1, d1) == (F(1), F(0))
assert w0[0] == w1[0] == F(1, 2)
assert normsq(w1) <= 4 and normsq(d1) <= 4
assert normsq(add(w1, (-F(1, 2), F(0)))) == 1 > F(1, 64)
# A valid ideal L=0 measurement with nonzero bounded errors, followed by
# arbitrary allowed nuisance phase. It refutes reuse of the .6 fixed-phase bound.
w, d, e0, e1 = F(19, 40), F(5, 8), -F(1, 10), F(1, 40)
b, z = F(1), F(1, 2)
assert w + d + e0 == b and w + e1 == z
assert abs(w - z - d) == F(13, 20) > F(3, 5)
assert abs(w - z - d) < F(3, 4)
ell, eps, K = F(1, 99), F(1, 40), F(3, 5)
B = (eps + ell * K) / (1 - ell)
Db = K + B
assert B == F(123, 3920) and Db == F(495, 784)
assert B + Db == F(1299, 1960) < F(3, 4)
# Real-valued sensor images: N=10 wheel cycles and one relative beat.
N = 10
real_leak = F(1, 99) + F(1, 100 * (2 * N + 1) - 1)
real_noise = 2 * eps
assert real_leak == F(2198, 207801)
assert 2 * real_leak + real_noise < F(1, 8)
result = {
    "quadrature_failure": {
        "same_complex_baseline": ["1", "0"],
        "same_separating_real_part": "1/2",
        "missed_corrected_wheel_norm_squared": "1",
        "limit_squared": "1/64",
    },
    "arbitrary_post_phase_counterexample": {
        "w": str(w),
        "d": str(d),
        "e0": str(e0),
        "e1": str(e1),
        "post_phase_multiplier": "-1",
        "mixed_residual": "13/20",
        "old_fixed_phase_bound": "3/5",
    },
    "joint_bounds": {"wheel": str(B), "nuisance": str(Db), "phase_free_mixed": str(B + Db)},
    "real_sensor_N10": {
        "leakage_bound": str(real_leak),
        "demod_noise_bound": str(real_noise),
        "wheel_bound_using_prior_D2": str(2 * real_leak + real_noise),
    },
    "scope": "Exact declared measurement-model fixtures. No physical actuator safety, source invariance or analytic-signal implementation established.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(
    "Exact quadrature failure, post-phase counterexample, coupled bounds and real-sensor budget pass"
)
