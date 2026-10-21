"""Independent adjoint bound on all compatible H and symmetric amplification."""

import json
import runpy
from fractions import Fraction as F
from pathlib import Path

BASE = Path(__file__).parent
d = runpy.run_path(str(BASE / "domain_exact.py"), run_name="critic_import")
mul, sub, scale, trans = d["mul"], d["sub"], d["scale"], d["transpose"]
eye, blocks, inner = d["identity"], d["blocks"], d["inner"]
k = blocks([1, 2, 3])
w = blocks([1, 0, 0])
q0 = d["zeros"]()
for i, j in enumerate([2, 3, 0, 1, 4, 5]):
    q0[i][j] = F(1)
rows = []
for den in [2, 4, 8, 16, 32, 64]:
    t = F(1, den)
    c, s = (1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)
    u = eye()
    u[0][0] = u[4][4] = c
    u[0][4], u[4][0] = s, -s
    q = mul(mul(u, q0), trans(u))
    y = mul(mul(q, k), q)
    assert mul(q, q) == eye()
    assert inner(k, k) == inner(y, y) == 28
    rhs = d["rhs"](k, y)
    adj = sub(mul(mul(y, k), w), mul(w, mul(k, y)))
    b = inner(w, rhs)
    aa = inner(adj, adj)
    lower_h2 = b * b / aa
    lower_s2 = F(1, 2) + 2 * lower_h2 / 28
    source = json.loads((BASE / "inventor_perturb.json").read_text())
    old = next(r for r in source if r["t"] == str(t))
    assert lower_h2 == F(old["H_frobenius_squared_lower_bound"])
    assert aa == F(old["adjoint_norm_squared"])
    # Independent numerical-free rank calculation and all 315 adjoint identities.
    check = d["audit"]("gate_" + str(t), k, y)
    assert check["consistent"]
    rows.append(
        {
            "t": str(t),
            "H_squared_lower": str(lower_h2),
            "s_squared_lower": str(lower_s2),
            "rules_out_s_less_than_one": lower_s2 >= 1,
            "rank": check["phi_rank"],
        }
    )
assert [r["rules_out_s_less_than_one"] for r in rows] == [False, True, True, True, True, True]
(BASE / "critic_gate_results.json").write_text(json.dumps(rows, indent=2) + "\n")
print(json.dumps(rows, indent=2))
