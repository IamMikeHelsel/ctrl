"""Independent exact certificate consumer for the fixed complex disk fixture."""

import copy
import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).parent


def verify(data):
    b, z = map(F, (data["observations"]["b"], data["observations"]["z"]))
    assert F(data["correction"]) == -z
    E0, E1, ell = F(1, 10), F(1, 40), F(1, 99)
    K = abs(b - z) + E0
    B = (E1 + ell * K) / (1 - ell)
    D = K + B
    bounds = data["bounds"]
    assert F(bounds["joint_wheel"]) == B
    assert F(bounds["nuisance_magnitude"]) == D
    assert F(bounds["arbitrary_post_nuisance_phase_mixed"]) == B + D
    assert B <= F(1, 8) and B + D <= F(3, 4)
    r = data["sharp_abstract_witness"]
    w, d, L, e0, e1 = [F(r[k]) for k in ["w", "d", "L", "e0", "e1"]]
    assert abs(w) <= 2 and abs(d) <= 2 and abs(L) <= ell
    assert abs(e0) <= E0 and abs(e1) <= E1
    assert b == w + d + e0 and z == w + L * d + e1
    assert abs(w - z - d) == B + D
    return B, D, B + D


data = json.loads((P / "pm_joint_gate.json").read_text())
B, D, M = verify(data)
mutations = []
for section, key, value in [
    ("bounds", "joint_wheel", "0"),
    ("sharp_abstract_witness", "L", "0"),
    ("observations", "b", "2"),
    (None, "correction", "1/2"),
]:
    bad = copy.deepcopy(data)
    if section:
        bad[section][key] = value
    else:
        bad[key] = value
    try:
        verify(bad)
    except AssertionError:
        mutations.append(key)
    else:
        raise AssertionError("corruption accepted")
eta = F(data["sufficient_eta_threshold"])
ell = eta / (1 - eta)
assert F(3, 5) + 2 * (F(1, 40) + ell * F(3, 5)) / (1 - ell) == F(3, 4)
report = {
    "status": "pass",
    "joint_wheel": str(B),
    "nuisance": str(D),
    "mixed": str(M),
    "mutations_rejected": mutations,
    "scope": "Independent fixed-artifact rational witness validation, not physical acquisition or general certificate-language implementation.",
}
(P / "critic_joint.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
