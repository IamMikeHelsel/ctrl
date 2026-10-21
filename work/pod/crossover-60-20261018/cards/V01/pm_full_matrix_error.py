"""Exact full-row uncertainty fixture, with a sharp rational image-error witness."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

P = Path(__file__).resolve().parent
H = [[F(3, 5), 0, F(9, 10)], [0, 1, F(1, 20)], [F(-4, 5), 0, F(4, 5)]]
eps = F(1, 1000)
e = F(7, 4000)
height = F(1593, 4000)
B = [F(28, 1593), F(49, 6372)]
assert [e * (1 + m) / height for m in [F(3), F(3, 4)]] == B
rows = []
maxerr = [F(0), F(0)]
for u, v in product([F(-1, 2), F(1, 2)], [F(-1, 4), F(1, 4)]):
    p = [u, v, F(1)]
    q = [sum(a * x for a, x in zip(row, p, strict=True)) for row in H]
    for signs in product([-1, 1], repeat=9):
        A = [[F(H[i][j]) + eps * signs[3 * i + j] for j in range(3)] for i in range(3)]
        qp = [sum(a * x for a, x in zip(row, p, strict=True)) for row in A]
        assert qp[2] >= height
        errors = [abs(qp[i] / qp[2] - q[i] / q[2]) for i in range(2)]
        assert all(z <= b for z, b in zip(errors, B, strict=True))
        maxerr = [max(a, b) for a, b in zip(maxerr, errors, strict=True)]
        if errors == B:
            rows.append({"uv": [u, v], "signs": signs, "errors": errors})
assert maxerr == B and rows
out = {
    "all_nine_entries_abs_error": eps,
    "corner_cases": 4 * 512,
    "maximum_corner_errors": maxerr,
    "universal_hand_bound": B,
    "attaining_witnesses": rows,
    "hand_proof": "For any patchpoint, each row error ≤7/4000. Exact quotient difference=(delta_i-image_i*delta_z)/(height+delta_z); image coordinate bounds3 and3/4 and perturbedheight≥1593/4000 imply bounds. Both attained at a declared corner.",
    "scope": "Uncertainty of the complete normalized homography in a fixed gauge; not implied by third-row-only guard, estimated calibration, physical decomposition or pixel-noise validation.",
}
(P / "pm_full_matrix_error.json").write_text(json.dumps(out, default=str, indent=2) + "\n")
print(json.dumps({"cases": out["corner_cases"], "bounds": B, "witnesses": len(rows)}, default=str))
