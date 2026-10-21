"""Independent 4-real-dimensional replay of the PM complex2D pair diagnostic."""

import json
from fractions import Fraction as Q
from pathlib import Path

from critic_adjoint import I, K, W, add, mul, scale, transpose

HERE = Path(__file__).resolve().parent
rows = []
for z in map(Q, [0, "1/4", "-1/4", "1/3", "1/2", 2, -2]):
    a, b = (1 + z * z) / (1 - z * z), 2 * z / (1 - z * z)
    s = add(scale(a, I), scale(b, W))
    si = scale(1 / (a * a + b * b), add(scale(a, I), scale(-b, W)))
    h = mul(K, add(I, scale(2 * a * b, W)))
    rows.append((2 * a * b, s, si, h))
count = nonunitary = 0
for t, s, si, h in rows:
    for _, r, ri, g in rows:
        c = mul(si, r)
        ci = mul(ri, s)
        kn = mul(mul(transpose(c), K), c)
        kinv = mul(mul(ci, K), transpose(ci))
        hn = mul(mul(transpose(c), h), c)
        wn = mul(mul(ci, W), c)
        assert hn == g and mul(kn, kinv) == I
        decorated = mul(wn, add(mul(kinv, hn), scale(-1, I)))
        assert sum(decorated[i][i] for i in range(4)) / 2 == -2 * t
        nonunitary += kn != K
        count += 1
producer = json.loads((HERE / "pm_pairs.json").read_text())
assert count == producer["pairs"] == 49
assert nonunitary == producer["non_K_unitary_coordinate_maps"] == 40
out = {
    "pairs": count,
    "non_K_unitary_maps": nonunitary,
    "representation": "4D realification; real trace/2 is complex trace",
    "result": "All49 independently verified; no producer routines imported.",
}
(HERE / "critic_pairs.json").write_text(json.dumps(out, indent=2) + "\n")
print(out)
