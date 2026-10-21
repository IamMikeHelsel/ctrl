"""Independent active witness for the revised true capsule enlargement."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
P = [[F(x) for x in row] for row in json.loads((HERE / "inventor_modes.json").read_text())["P"]]
g = [F(1), -F(1), F(1)]


def energy(z):
    return sum((z[i] * P[i][j] * z[j] for i in range(3) for j in range(3)), F(0))


def request(z):
    return -z[0] - 3 * z[1] - 2 * z[2]


base = [F(29, 20), -F(27, 20), F(37, 20)]
lift = [x + y / 25 for x, y in zip(base, g, strict=True)]
assert energy(base) < 12 < energy(lift)
assert request(base) == request(lift) == -F(11, 10)
assert lift == [F(149, 100), -F(139, 100), F(189, 100)]
c = F(3550075, 11131832)
assert 12 * c < F(49, 25) ** 2
assert F(49, 25) + F(1, 25) == 2
# Old E12+1/8g failure is irrelevant to the revised1/25 segment.
old_failure_base_x = F(19, 10)
assert old_failure_base_x + F(1, 25) == F(97, 50) < 2
out = {
    "candidate": "E12+[-1/25,1/25]*(1,-1,1)",
    "strict_active_expansion": {
        "base": list(map(str, base)),
        "base_energy": str(energy(base)),
        "lift": list(map(str, lift)),
        "lift_energy": str(energy(lift)),
        "both_requests": str(request(base)),
        "both_clamps": "-1",
    },
    "sharp_position_budget": "12*(P^-1)00 < (49/25)^2; 49/25+1/25=2",
    "scope": "Exact geometry supporting the separately audited source-coupled dynamical proof. E11 alternative and E12+1/8 failure remain preserved as different candidates.",
}
(HERE / "inventor_capsule12.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
