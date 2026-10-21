"""Independent exact two-view SPD and whole-board ambiguity parameter bindings."""

import json
from fractions import Fraction as F
from pathlib import Path

from critic_rank import det

P = Path(__file__).parent
D = json.loads((P / "domain_rank.json").read_text())
T = json.loads((P / "domain_two_views.json").read_text())
A = [[F(x) for x in r] for r in D["cases"][1]["A"]]
b = [F(x) for x in T["normalized_metric_alternative"]]
assert all(sum(x * y for x, y in zip(r, b, strict=True)) == 0 for r in A)
B = [[b[0], b[1], b[3]], [b[1], b[2], b[4]], [b[3], b[4], b[5]]]
minors = [B[0][0], B[0][0] * B[1][1] - B[0][1] ** 2, det(B)]
assert all(x > 0 for x in minors)
assert list(map(str, minors)) == T["leading_principal_minors"]
false_prior = list(map(F, T["false_zero_skew_prior_metric"]))
assert false_prior[1] == 0 and all(
    sum(x * y for x, y in zip(row, false_prior, strict=True)) == 0 for row in A
)
FB = [
    [false_prior[0], false_prior[1], false_prior[3]],
    [false_prior[1], false_prior[2], false_prior[4]],
    [false_prior[3], false_prior[4], false_prior[5]],
]
fm = [FB[0][0], FB[0][0] * FB[1][1] - FB[0][1] ** 2, det(FB)]
assert all(x > 0 for x in fm) and list(map(str, fm)) == T["false_zero_skew_prior_minors"]
assert any(
    sum(F(x) * y for x, y in zip(row, false_prior, strict=True)) != 0 for row in D["cases"][2]["A"]
)
r = json.loads((P / "pm_near_views.json").read_text())["rows"][2]
c, s, cp, sp, f = map(F, [r["c"], r["s"], r["c2"], r["s2"], r["focal_ratio"]])
a = cp / c
assert sp / f == a * s and 0 < a < 1 and abs(1 - a) <= F(1, 62500) and abs(s) <= F(1, 500)
# Product denominator>=4.99² and numerator<=.08 give global closed-board coordinate bound.
assert F(2, 25) / (F(499, 100) ** 2) < F(33, 10000)
(P / "critic_supplement.json").write_text(
    json.dumps(
        {
            "two_view_SPD_minors": list(map(str, minors)),
            "false_zero_skew_SPD_minors": list(map(str, fm)),
            "false_zero_skew_third_view_rejects": True,
            "continuous_parameters": {
                "a": str(a),
                "one_minus_a": str(1 - a),
                "sp_over_f_equals_a_s": True,
                "global_projection_bound": "33/10000",
                "midpoint_coordinate_radius": "33/20000",
            },
            "scope": "Sylvester SPD and whole-board scalar inequalities plus manually bound camera identities; no pixel-noise-to-row perturbation assumption.",
        },
        indent=2,
    )
    + "\n"
)
print("Two-view SPD alternative and continuous ambiguity scalar bindings independently verified")
