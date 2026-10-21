"""Independent witness/hand-bound arithmetic for complete normalized-H errors."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent
j = json.loads((P / "pm_full_matrix_error.json").read_text())
H = [[F(3, 5), 0, F(9, 10)], [0, 1, F(1, 20)], [F(-4, 5), 0, F(4, 5)]]


def mv(a, x):
    return [sum(t * s for t, s in zip(r, x, strict=True)) for r in a]


eps = F(1, 1000)
rowbound = eps * (F(1, 2) + F(1, 4) + 1)
lower = F(2, 5) - rowbound
assert lower == F(1593, 4000)
bound = [rowbound * (1 + m) / lower for m in [F(3), F(3, 4)]]
assert bound == list(map(F, j["universal_hand_bound"])) == [F(28, 1593), F(49, 6372)]
for w in j["attaining_witnesses"]:
    p = [*map(F, w["uv"]), F(1)]
    s = w["signs"]
    A = [[H[i][k] + eps * s[3 * i + k] for k in range(3)] for i in range(3)]
    q, qp = mv(H, p), mv(A, p)
    assert qp[2] > 0 and [abs(qp[i] / qp[2] - q[i] / q[2]) for i in range(2)] == bound
out = {
    "bound": list(map(str, bound)),
    "attaining_witnesses_checked": len(j["attaining_witnesses"]),
    "scope": "Universal quotient inequality checked by hand, rational arithmetic and attaining witness independently reconstructed. Not all camera physical parameters or homography gauge errors are bounded by this box.",
}
(P / "critic_full_error.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
