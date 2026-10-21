"""Exact prospective center selection using the saved C3 startup envelope."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

m = [F(".14"), F("-.01"), F("-1.17")]
R = F(2221, 40000)
D = F(1, 2000)
e = [F(".001") + F(".03065") * D, F(".01") + F("1.3") * D, F(".05") + F("30.24") * D]
A = [m[0], m[0] + m[1] / 4, m[0] + m[1] / 2 + m[2] / 16]
b = [e[0], e[0] + e[1] / 4, e[0] + e[1] / 2 + e[2] / 16]
U, L = max(a + w for a, w in zip(A, b, strict=True)), min(a - w for a, w in zip(A, b, strict=True))
old = m[0] + m[1] / 4 + m[2] / 32
optimal = (L + U) / 2
forward = U - R + F(".001")
rows = []
for name, c in [("old", old), ("minimax", optimal), ("forward", forward)]:
    maximum = max(abs(a - c) + w for a, w in zip(A, b, strict=True))
    for signs in product([-1, 1], repeat=3):
        state = [x + sg * w for x, sg, w in zip(m, signs, e, strict=True)]
        z = [state[0] - c, state[0] - c + state[1] / 4, state[0] - c + state[1] / 2 + state[2] / 16]
        assert max(map(abs, z)) <= maximum
    rows.append(
        {
            "name": name,
            "center": str(c),
            "startup_box_radius": str(maximum),
            "fixed_R_upper_tube": str(c + R),
            "first_read_command": str(-8 * (m[0] - c) - 6 * m[1] - m[2] / 2),
        }
    )
assert forward + R == F(".142177825") and optimal == F(".09632125")
assert (U - L) / 2 == F(".044856575")
# A center beyond the feasible interval fails an attained single facet.
invalid = U - R - F(".000001")
assert U - invalid > R
out = {
    "U": str(U),
    "L": str(L),
    "rows": rows,
    "corners_per_center": 8,
    "center_below_feasible_interval_rejected": True,
    "scope": "Exact independent-startup-envelope geometry with changed center policy; not a new Execution or all-time hold theorem. No joint-corner attainability assumption.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
