"""Exact block-linear two-injection-parameter determinant, fixed A3-A5 outputs."""

import json
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

import pm_symbol as m
from pm_exact_det import bareiss, components, parity

P = Path(__file__).resolve().parent


def read(k):
    data = json.loads((P / f"pm_matrix_A_{k}.json").read_text())
    return [{j: int(v) for j, v in row} for row in data["rows"]]


a = read(4)
b = read(5)
groups = components(a, 448)
constant = parity([i for r, _ in groups for i in r]) * parity([i for _, c in groups for i in c])
counts = Counter()
blocks = []
for rs, cs in groups:
    da = bareiss([[a[i].get(j, 0) for j in cs] for i in rs])
    db = bareiss([[b[i].get(j, 0) for j in cs] for i in rs])
    variable = [r for r in rs if 8 <= r < 64]
    if not variable:
        assert all(a[i] == b[i] for i in rs)
        assert da == db
        constant *= da
        kind = "constant"
    else:
        assert len(variable) == 1
        assert all(a[i] == b[i] for i in rs if i != variable[0])
        ratio = F(db, da)
        assert ratio in (F(6, 5), F(-3, 5))
        assert da % 5 == 0
        constant *= da // 5
        kind = "5a+6b" if ratio > 0 else "5a-3b"
    counts[kind] += 1
    blocks.append(
        {"rows": rs, "columns": cs, "a_coefficient": da, "b_coefficient": db, "kind": kind}
    )
assert counts == {"constant": 8, "5a+6b": 21, "5a-3b": 35}
assert constant == 2**491 * 3**43 * 5**21 * 7**8
checks = []
for aa, bb in [(2, -1), (3, 5), (6, -5), (-1, -2)]:
    c = [aa, bb, 1, 1, -1, 1, 1, 1, 1, -1]
    matrix = m.matrix(c)
    rows = [{j: int(x) for j, x in enumerate(row) if x} for row in matrix]
    expected = constant * (5 * aa + 6 * bb) ** 21 * (5 * aa - 3 * bb) ** 35
    actual = parity([i for r, _ in groups for i in r]) * parity([i for _, c in groups for i in c])
    for rs, cs in groups:
        actual *= bareiss([[rows[i].get(j, 0) for j in cs] for i in rs])
    assert all(
        rows[i].get(j, 0)
        == (aa * a[i].get(j, 0) + bb * b[i].get(j, 0) if 8 <= i < 64 else a[i].get(j, 0))
        for i in range(448)
        for j in range(448)
    )
    assert actual == expected
    checks.append({"a": aa, "b": bb, "exact_match": True, "determinant_zero": actual == 0})
result = {
    "fixed_output_coefficients": [1, 1, -1, 1, 1, 1, 1, -1],
    "formula": "2^491 * 3^43 * 5^21 * 7^8 * (5a+6b)^21 * (5a-3b)^35",
    "block_counts": dict(counts),
    "constant": str(constant),
    "blocks": blocks,
    "heldout_checks": checks,
    "scope": "Exact determinant identity for source-reconstructed matrix under explicit per-row affine coefficient structure; not kernel checked or resolution of printed sign discrepancy.",
}
(P / "pm_two_parameter.json").write_text(json.dumps(result, indent=2) + "\n")
print(result["formula"])
print(checks)
