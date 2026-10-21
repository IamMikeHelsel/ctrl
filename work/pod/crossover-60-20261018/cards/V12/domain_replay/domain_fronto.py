"""Two physically different intrinsic matrices explain every fronto-parallel fixture."""

import json
from fractions import Fraction as F
from pathlib import Path

p = Path(__file__).parent
r = json.loads((p / "domain_rank.json").read_text())
K = [[F(x) for x in row] for row in r["K"]]
Kalt = [[v * (2 if j < 2 else 1) for j, v in enumerate(row)] for row in K]
I = [[F(i == j) for j in range(3)] for i in range(3)]
Rz = [[F(3, 5), F(-4, 5), F(0)], [F(4, 5), F(3, 5), F(0)], [F(0), F(0), F(1)]]


def mul(A, B):
    return [
        [sum(x * y for x, y in zip(row, col, strict=True)) for col in zip(*B, strict=True)]
        for row in A
    ]


rows = []
for j, R in enumerate([I, Rz, mul(Rz, Rz)]):
    t = [F(j, 4), F(-j, 3), F(4 + j)]
    talt = [t[0], t[1], 2 * t[2]]
    H = mul(K, [[R[i][0], R[i][1], t[i]] for i in range(3)])
    Ha = mul(Kalt, [[R[i][0], R[i][1], talt[i]] for i in range(3)])
    assert Ha == [[2 * x for x in row] for row in H]
    assert t[2] > 0 and talt[2] > 0
    rows.append({"translation": t, "alternative_translation": talt, "H": H, "H_alt": Ha})
result = {
    "K": K,
    "K_alt": Kalt,
    "cases": rows,
    "image_equality": "H_alt=2H; all finite board images identical",
    "scope": "Known metric plane, unknown camera-to-board distance, exact undistorted pinhole; same positive orientations.",
}
(p / "domain_fronto.json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print("Three physically valid fronto-parallel ambiguities checked.")
