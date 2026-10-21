"""Exact precision-to-action design analysis; original frozen data unchanged."""

import json
from fractions import Fraction as F
from pathlib import Path

from inventor_exact import accept, actions, constraints, enc, observation, vertices


def evaluate(epsilon):
    branches = {
        str(sign): vertices(constraints(sign) + observation("separating", epsilon))
        for sign in [1, -1]
    }
    envelope = actions(branches)
    lo = (F(59, 200) - epsilon) / F(7, 10)
    hi = (F(89, 200) + epsilon) / F(4, 5)
    assert envelope["wheel_range"] == [lo, hi]
    assert not branches["-1"]
    assert hi - lo == F(151, 1120) + F(75, 28) * epsilon
    assert bool(envelope["safe_interval"]) == (epsilon <= F(43, 1000))
    assert accept(branches, F(-1, 2)) == (epsilon <= F(13, 400))
    # Feasible endpoint witnesses make attainability independent of vertex labels.
    low_world = (lo, F(11, 10) - lo, F(3, 10) * (F(11, 10) - lo))
    high_world = (hi, F(9, 10) - hi, F(1, 5) * (F(9, 10) - hi))
    cs = constraints(1) + observation("separating", epsilon)
    assert all(
        sum(a * x for a, x in zip(row, p, strict=True)) <= b
        for p in [low_world, high_world]
        for row, b in cs
    )
    return {
        "separating_error_radius": epsilon,
        "envelope": envelope,
        "original_minus_half_accepted": accept(branches, F(-1, 2)),
        "endpoint_witnesses": [low_world, high_world],
    }


radii = [F(0), F(1, 40), F(13, 400), F(33, 1000), F(43, 1000), F(11, 250), F(1, 10)]
rows = [evaluate(e) for e in radii]
assert rows[4]["envelope"]["safe_interval"] == [F(-97, 200), F(-97, 200)]
result = {
    "design_scope": "Change only stated error guarantee of an actually separating observation; this is prospective analysis, not reinterpretation of frozen data or permission to execute new corrections.",
    "analytic_domain": "0 <= epsilon <= 1/10",
    "wheel_width_formula": "151/1120 + (75/28)*epsilon",
    "some_correction_threshold": "43/1000",
    "original_minus_half_threshold": "13/400",
    "tests": rows,
}
Path(__file__).with_name("inventor_design.json").write_text(
    json.dumps(enc(result), indent=2) + "\n"
)
print(json.dumps(enc(result), indent=2))
