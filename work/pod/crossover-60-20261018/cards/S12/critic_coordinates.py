"""Independent decision-summary checks using previously verified source supports."""

import json
from fractions import Fraction as F
from pathlib import Path

BASE = Path(__file__).parent
SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution/results.json"
)
source = json.loads(SOURCE.read_text())["stages"]["separated"]["ranges"]
wlo, whi = map(F, source["wheel"])
dlo, dhi = map(F, source["drivetrain"])
blo, bhi = map(F, source["baseline_response"])
c = F(-1, 2)
wrong_source_upper = whi + dhi + c
mixed = [min(wlo, blo) + c, max(whi, bhi) + c]
lo = max(-F(1, 8) - wlo, -F(3, 4) - min(wlo, blo))
hi = min(F(1, 8) - whi, F(3, 4) - max(whi, bhi))
saved = json.loads((BASE / "inventor_coordinates.json").read_text())
if (
    wrong_source_upper != F(saved["source_box_mixed_upper_for_original_action"])
    or mixed != list(map(F, saved["decision_box_mixed_range_for_original_action"]))
    or [lo, hi] != list(map(F, saved["decision_box_exact_safe_action_interval"]))
):
    raise ValueError("coordinate result mismatch")
# A decision-summary corner passes both marginal supports but has no original world.
phantom_w, phantom_b = wlo, blo
phantom_d = phantom_b - phantom_w
max_q = F(3, 10) * phantom_d
if not (
    wlo <= phantom_w <= whi
    and blo <= phantom_b <= bhi
    and phantom_d == F(18, 35)
    and phantom_w + max_q == F(27, 50) < F(3, 5)
):
    raise ValueError("phantom-corner counterexample failed")
# Counterexample to a readout-independent precision promise: replace observation center.
new_center = F(-3, 10)
worlds = [(F(-9, 10), F(2), F(3, 5)), (F(-3, 5), F(3, 2), F(3, 10))]
for w, d, q in worlds:
    if not (
        -2 <= w <= 2
        and -2 <= d <= 2
        and F(1, 5) <= q / d <= F(3, 10)
        and F(9, 10) <= w + d <= F(11, 10)
        and w + q == new_center
    ):
        raise ValueError("changed-readout endpoint invalid")
if worlds[1][0] - worlds[0][0] != F(3, 10) > F(1, 4):
    raise ValueError("common correction impossibility failed")
# Interval sum property: two residuals each in[-1/8,1/8] differ by at most1/4.
# Actual difference3/10 is invariant under any common correction.
result = dict(
    decision_mixed_range=list(map(str, mixed)),
    safe_action_interval=list(map(str, [lo, hi])),
    source_box_upper=str(wrong_source_upper),
    phantom_summary_corner=dict(
        w=str(phantom_w),
        b=str(phantom_b),
        d=str(phantom_d),
        max_q=str(max_q),
        max_separating_readout=str(phantom_w + max_q),
        required_lower="3/5",
    ),
    precision_counterexample=dict(
        changed_center=str(new_center),
        error_radius="0",
        worlds=[[str(x) for x in p] for p in worlds],
        wheel_gap="3/10",
        maximum_gap_for_common_correction="1/4",
    ),
    scope="Decision abstraction exact only for frozen all-rho action predicate; cannot replace joint belief for updates. Precision thresholds condition on readout center5/8.",
)
(BASE / "critic_coordinates_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
