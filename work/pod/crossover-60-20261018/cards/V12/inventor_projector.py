"""Exact projective-gauge invariant rowspace coverage; not a noise covariance model."""

import json
from fractions import Fraction as F
from pathlib import Path


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def projector(a):
    gram = [[dot(x, y) for y in a] for x in a]
    d = gram[0][0] * gram[1][1] - gram[0][1] ** 2
    assert d > 0
    inv = [[gram[1][1] / d, -gram[0][1] / d], [-gram[1][0] / d, gram[0][0] / d]]
    p = [
        [sum(a[k][i] * inv[k][l] * a[l][j] for k in range(2) for l in range(2)) for j in range(6)]
        for i in range(6)
    ]
    assert all(
        dot(p[i], [p[k][j] for k in range(6)]) == p[i][j] for i in range(6) for j in range(6)
    )
    assert sum(p[i][i] for i in range(6)) == 2
    assert all(dot(row, p[j]) == row[j] for row in a for j in range(6))
    return p


path = Path(__file__)
source = json.loads(path.with_name("inventor_metric.json").read_text())
a = [[F(x) for x in row] for row in source["constraints"]]
output = []
for v in range(3):
    rows = a[2 * v : 2 * v + 2]
    p = projector(rows)
    base_gram_trace = sum(dot(row, row) for row in rows)
    tests = []
    for scale in [F(1, 100), F(-3), F(100)]:
        scaled = [[scale**2 * x for x in row] for row in rows]
        assert projector(scaled) == p
        ratio = sum(dot(row, row) for row in scaled) / base_gram_trace
        assert ratio == scale**4
        tests.append({"H_scale": scale, "raw_gram_trace_ratio": ratio, "projector_unchanged": True})
    # A change of generators for the same 2D constraint space also preserves coverage.
    mixed = [
        [2 * x + 3 * y for x, y in zip(*rows, strict=True)],
        [x + 2 * y for x, y in zip(*rows, strict=True)],
    ]
    assert projector(mixed) == p
    output.append({"view": v, "rowspace_projector": p, "metamorphic_tests": tests})
null = [F(x) for x in source["null_vector"]]
combined = [
    [sum(case["rowspace_projector"][i][j] for case in output) for j in range(6)] for i in range(6)
]
assert all(dot(row, null) == 0 for row in combined)
path.with_suffix(".json").write_text(
    json.dumps(
        {
            "cases": output,
            "summed_projector": combined,
            "meaning": "Each P is a geometric rowspace projector in the declared Euclidean b-coordinate chart.",
            "limits": [
                "Not Fisher information or calibrated uncertainty without residual/noise model.",
                "Nonorthogonal parameter or pixel coordinate changes require an explicit metric transform.",
                "Repeated/correlated views change projector sum weights, not independent information.",
            ],
        },
        default=str,
        indent=2,
    )
    + "\n"
)
print({"views": len(output), "gauge_tests": 9, "basis_change_tests": 3, "trace_per_view": 2})
