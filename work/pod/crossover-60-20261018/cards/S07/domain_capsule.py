"""Exact support witness and bounded volume comparison for the proposed capsule."""

import json
from fractions import Fraction as F
from math import sqrt
from pathlib import Path

p = Path(__file__).parent
geo = json.loads((p / "domain_geometry.json").read_text())
P = [[F(x) for x in row] for row in geo["P"]]
Pinv = [[F(x) for x in row] for row in geo["P_inverse"]]
g = [F(1), F(-1), F(1)]
n = [F(1), F(1), F(0)]
sigma = sum(n[i] * Pinv[i][j] * n[j] for i in range(3) for j in range(3))
y = [sum(Pinv[i][j] * n[j] for j in range(3)) for i in range(3)]
# A rational point on the p-normal ellipsoid direction, avoiding radical witnesses.
t = F(7)
z = [t * v for v in y]
V = t * t * sigma
assert 11 < V <= 12
projection = sum(n[i] * z[i] for i in range(3))
assert projection**2 > 11 * sigma
assert sum(n[i] * g[i] for i in range(3)) == 0
q = sum(g[i] * P[i][j] * g[j] for i in range(3) for j in range(3))
assert q == F(189, 50)
d = F(1, 8)
# After dividing out pi/sqrt(detP), volumes are4/3*R^(3/2)+2*d*R*sqrt(q).
ratio = (11 / 12) ** 1.5 + 3 * float(d) * 11 * sqrt(float(q)) / (2 * 12**1.5)
# Exact outward radical bounds; strict inequalities verified by squaring.
u11, uq, l12 = F(3317, 1000), F(1945, 1000), F(3464, 1000)
assert u11 * u11 > 11 and uq * uq > q and l12 * l12 < 12
upper_ratio = (44 * u11 + F(33, 4) * uq) / (48 * l12)
assert upper_ratio < 1
out = {
    "definition": "K=E11+[-1/8,1/8]g; g=(1,-1,1)",
    "support_formula": "hK(p)=sqrt(11*p^T*P^-1*p)+(1/8)*abs(p dot g)",
    "E12_not_subset_K": {
        "normal": list(map(str, n)),
        "sigma": str(sigma),
        "z": list(map(str, z)),
        "V": str(V),
        "projection_squared": str(projection**2),
        "capsule_projection_squared_bound": str(11 * sigma),
    },
    "K_not_subset_E12": {"z": ["73/40", "-73/40", "73/40"], "V": "1007181/80000"},
    "g_P_g": str(q),
    "volume_ratio_to_E12": ratio,
    "rigorous_volume_ratio_upper": str(upper_ratio),
    "volume_formula": "volK=(pi/sqrt(detP))*(4/3*11^(3/2)+11/4*sqrt(189/50))",
    "scope": "Minkowski-sum and projection-volume formula hand-derived; arithmetic exact except labeled ratio.",
}
(p / "domain_capsule.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))

# Better variant: preserve the original certified core, use its sharp unused travel margin.
delta = F(1, 25)
assert 12 * F(3550075, 11131832) < F(49, 25) ** 2
coreq, liftq = F(89, 50), F(91, 50)
assert liftq - coreq == delta
coreV, liftV = q * coreq**2, q * liftq**2
assert coreV < 12 < liftV
out["strict_superset_variant"] = {
    "definition": "E12+[-1/25,1/25]g",
    "core_position_bound": "49/25",
    "core_witness_scale": str(coreq),
    "lift_witness_scale": str(liftq),
    "core_witness_energy": str(coreV),
    "lift_witness_energy": str(liftV),
    "volume_ratio_exact": "1+(3/50)*sqrt(63/200)",
    "volume_ratio_approx": 1 + F(3, 50) * sqrt(F(63, 200)),
    "scope": "Strict superset and source-bound geometric margin; same-mode execution bridge separate.",
}
(p / "domain_capsule.json").write_text(json.dumps(out, indent=2) + "\n")
print(out["strict_superset_variant"])

base = [F(x) for x in geo["input2_min_energy_witness"]]
core = [x + F(11, 20) * v for x, v in zip(base, g, strict=True)]
lift = [x + F(1, 25) * v for x, v in zip(core, g, strict=True)]


def energy(z):
    return sum(z[i] * P[i][j] * z[j] for i in range(3) for j in range(3))


assert energy(core) < 12 < energy(lift)
assert -core[0] - 3 * core[1] - 2 * core[2] == -lift[0] - 3 * lift[1] - 2 * lift[2] == 2
active = {
    "core": list(map(str, core)),
    "lift": list(map(str, lift)),
    "core_energy": str(energy(core)),
    "lift_energy": str(energy(lift)),
    "input_both": "2",
    "clamp_both": "1",
    "offset": "(1/25)*(1,-1,1)",
}
(p / "domain_capsule_active.json").write_text(json.dumps(active, indent=2) + "\n")
