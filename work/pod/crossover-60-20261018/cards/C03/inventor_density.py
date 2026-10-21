"""Bounded-density transport diagnostic for snap-limited endpoint moments."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
# μ=(snap+1)dt; for initial/finalj0,T1: μmass=1.
# At aT0, μmean=1/2. A Dirac relaxation gives variance0 and a false endpoint.
moments = [F(1, 2) ** k for k in range(4)]
a = F(1, 2) - moments[1]
v = (moments[2] - F(1, 3) + 2 * a) / 2
# q=1/6∫(1-t)^3 (dμ-dt).
q = (moments[0] - 3 * moments[1] + 3 * moments[2] - moments[3] - F(1, 4)) / 6
assert (q, v, a) == (-F(1, 48), -F(1, 24), F(0))
assert moments[0] * moments[2] - moments[1] ** 2 == 0
assert moments[1] * moments[3] - moments[2] ** 2 == 0


# Bounded-density rearrangement: μdensity in[0,2], mass1.
# With h=(t-.5)^2-.0625, h<0 exactly on[.25,.75].
def primitive(t):
    return (t - F(1, 2)) ** 3 / 3 - t / F(16)


negative_region_integral = primitive(F(3, 4)) - primitive(F(1, 4))
assert negative_region_integral == -F(1, 48)
variance_lower = F(1, 16) + 2 * negative_region_integral
assert variance_lower == F(1, 48)
# μdensity2 on[1/4,3/4] attains the lower bound and has mean1/2.
real_moments = [2 * (F(3, 4) ** (k + 1) - F(1, 4) ** (k + 1)) / (k + 1) for k in range(4)]
assert real_moments[0] == 1 and real_moments[1] == F(1, 2)
assert real_moments[2] - real_moments[1] ** 2 == F(1, 48)
real_v = (real_moments[2] - F(1, 3)) / 2
assert real_v == -F(1, 32)
# False relaxed endpoint violates the sharp mixed necessary condition.
assert a - 2 * v == F(1, 12) > F(1, 16)
out = {
    "scope": "Normalized diagnostic, not source stop task. Moment PSD is necessary, not a sufficient bounded-snap admission rule.",
    "false_measure_relaxation": {
        "moments_0_through_3": list(map(str, moments)),
        "q_v_a_j": list(map(str, [q, v, a, F(0)])),
        "Hankel_2x2_determinant": "0",
        "why_not_a_reference": "Dirac mass at1/2 violates μdensity<=2, hence cannot come from |snap|<=1.",
    },
    "retained_density_cap": {
        "variance_lower_bound": str(variance_lower),
        "sharp_velocity_lower_a0": str(real_v),
        "attaining_density": "2 on[1/4,3/4],0 elsewhere",
        "moments": list(map(str, real_moments)),
    },
}
(HERE / "inventor_density.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
