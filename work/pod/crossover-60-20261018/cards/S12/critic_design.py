"""Independent dual-style algebra and witness consumer for precision-to-action result."""

import copy
import json
from fractions import Fraction as F
from pathlib import Path

BASE = Path(__file__).parent
DATA = json.loads((BASE / "inventor_design.json").read_text())
EXPECTED = [F(0), F(1, 40), F(13, 400), F(33, 1000), F(43, 1000), F(11, 250), F(1, 10)]


def world_valid(p, epsilon, baseline_error=F(1, 10)):
    w, d, q = p
    return (
        -2 <= w <= 2
        and -2 <= d <= 2
        and d > 0
        and F(1, 5) <= q / d <= F(3, 10)
        and 1 - baseline_error <= w + d <= 1 + baseline_error
        and F(5, 8) - epsilon <= w + q <= F(5, 8) + epsilon
    )


def verify(data):
    if [F(r["separating_error_radius"]) for r in data["tests"]] != EXPECTED:
        raise ValueError("coverage")
    if F(data["some_correction_threshold"]) != F(43, 1000) or F(
        data["original_minus_half_threshold"]
    ) != F(13, 400):
        raise ValueError("threshold")
    for row in data["tests"]:
        epsilon = F(row["separating_error_radius"])
        lower = (F(5, 8) - epsilon - F(3, 10) * F(11, 10)) / F(7, 10)
        upper = (F(5, 8) + epsilon - F(1, 5) * F(9, 10)) / F(4, 5)
        if list(map(F, row["envelope"]["wheel_range"])) != [lower, upper]:
            raise ValueError("range")
        for witness, target in zip(row["endpoint_witnesses"], [lower, upper], strict=True):
            p = list(map(F, witness))
            if not world_valid(p, epsilon) or p[0] != target:
                raise ValueError("endpoint witness")
        action_lower = max(-F(1, 8) - lower, -F(3, 4) - min(lower, F(9, 10)))
        action_upper = min(F(1, 8) - upper, F(3, 4) - max(upper, F(11, 10)))
        envelope = [action_lower, action_upper] if action_lower <= action_upper else []
        if list(map(F, row["envelope"]["safe_interval"])) != envelope:
            raise ValueError("action envelope")
        if bool(envelope) != (epsilon <= F(43, 1000)):
            raise ValueError("threshold equivalence")
        fixed = bool(envelope) and action_lower <= -F(1, 2) <= action_upper
        if fixed != (epsilon <= F(13, 400)) or fixed != row["original_minus_half_accepted"]:
            raise ValueError("fixed action")
    return len(data["tests"])


count = verify(DATA)
negatives = []
for kind in ["coverage", "threshold", "witness", "envelope"]:
    bad = copy.deepcopy(DATA)
    if kind == "coverage":
        bad["tests"].pop()
    elif kind == "threshold":
        bad["some_correction_threshold"] = "44/1000"
    elif kind == "witness":
        bad["tests"][0]["endpoint_witnesses"][0][0] = "1/2"
    else:
        bad["tests"][4]["envelope"]["safe_interval"][0] = "-1/2"
    try:
        verify(bad)
    except ValueError as error:
        negatives.append(dict(mutation=kind, rejection=str(error)))
    else:
        raise ValueError("corruption accepted")
# Independent original-hull and false-confidence witnesses.
a = (F(1, 2), F(1, 2), F(1, 10))
b = (F(3, 2), F(-1, 2), F(-3, 20))
mid = tuple((x + y) / 2 for x, y in zip(a, b, strict=True))
if mid != (F(1), F(0), F(-1, 40)) or mid[2] == 0:
    raise ValueError("nonphysical midpoint")
witness = (F(47, 80), F(5, 16), F(1, 16))
if not world_valid(witness, F(1, 40)) or witness[0] - F(23, 50) != F(51, 400):
    raise ValueError("false precision witness")
# Universal analytic bounds use nonnegative combinations of original rows:
# upper: [separating upper]+[.2d-q<=0]+.2[-w-d<=-.9] -> .8w<=.445+epsilon.
# lower: [separating lower]+[q-.3d<=0]+.3[w+d<=1.1] -> -.7w<=-.295+epsilon.
# Negative branch implies w+q>=w+.3d>=.9>.625+epsilon for epsilon<=.1.
result = dict(
    rows_verified=count,
    negative_controls=negatives,
    universal_range_argument="Two nonnegative row combinations; feasible endpoint formulas; negative branch impossible for epsilon in[0,.1]. Hand algebra plus exact rational checks, not LP solver trust.",
    scope="Prospective separating-sensor precision analysis and continuous action-set extension, not reinterpretation of frozen observations or execution authorization.",
)
(BASE / "critic_design_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
