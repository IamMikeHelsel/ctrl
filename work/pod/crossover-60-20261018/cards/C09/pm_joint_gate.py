"""Exact decision envelope for a declared complex leakage disk; no hardware."""

import json
from fractions import Fraction as F
from pathlib import Path

E0, E1, ell = F(1, 10), F(1, 40), F(1, 99)
b, z = F(1), F(1, 2)
K = abs(b - z) + E0
old = E1 + 2 * ell
B = (E1 + ell * K) / (1 - ell)
D = K + B
mixed = K + 2 * B
assert old == F(179, 3960)
assert B == F(123, 3920)
assert D == F(495, 784)
assert mixed == F(1299, 1960)
assert B < F(1, 8) and mixed < F(3, 4)
# Sharpness for the relaxed real subset of the complex leakage disk.
w = z - B
d = D
e0 = -E0
e1 = E1
L = ell
assert b == w + d + e0 and z == w + L * d + e1
assert abs(w) <= 2 and abs(d) <= 2
assert abs(w - z - d) == mixed  # arbitrary final nuisance phase flip.
# Baseline indistinguishability: any shared correction has wheel radius >=1/2.
assert b == 0 + 1 == 1 + 0
# Discriminating perturbation: leakage bound from eta=.08 breaks mixed gate,
# while the abstract fixture remains nonempty and the wheel gate still passes.
eta = F(2, 25)
leak2 = eta / (1 - eta)
B2 = (E1 + leak2 * K) / (1 - leak2)
assert B2 < F(1, 8) and K + 2 * B2 > F(3, 4)
# Worst-case sufficient threshold of the final bound, not exact physical sinc optimum.
eta_star = F(2, 29)
leak_star = eta_star / (1 - eta_star)
Bstar = (E1 + leak_star * K) / (1 - leak_star)
assert K + 2 * Bstar == F(3, 4)
out = {
    "model": "b=w+d+e0, z=w+L*d+e1; complex norms, |w|,|d|<=2, errors1/10 and1/40, |L|<=1/99",
    "observations": {"b": str(b), "z": str(z)},
    "correction": str(-z),
    "bounds": {
        "prior_only_wheel": str(old),
        "joint_wheel": str(B),
        "nuisance_magnitude": str(D),
        "arbitrary_post_nuisance_phase_mixed": str(mixed),
        "wheel_slack": str(F(1, 8) - B),
        "mixed_slack": str(F(3, 4) - mixed),
    },
    "sharp_abstract_witness": {
        "w": str(w),
        "d": str(d),
        "L": str(L),
        "e0": str(e0),
        "e1": str(e1),
        "post_nuisance_phase": "pi",
    },
    "sufficient_eta_threshold": str(eta_star),
    "eta_2_over_25_negative": {
        "wheel_bound": str(B2),
        "mixed_bound": str(K + 2 * B2),
        "wheel_pass": True,
        "mixed_pass": False,
    },
    "scope": "Joint uncertainty retained; triangle-based bounds valid for every complex tuple. Sharpness witness is in relaxed leakage disk, not asserted attainable on exact constant-frequency sinc locus. Nuisance magnitude and wheel phase/transfer must remain bound.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
