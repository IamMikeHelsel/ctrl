"""Independent finite witness checks for changed-readout action conflicts."""

import json
from fractions import Fraction as F
from pathlib import Path

BASE = Path(__file__).parent
DATA = json.loads((BASE / "inventor_update_boundary.json").read_text())


def actions(world):
    w, d, _ = world
    lower = max(-F(1, 8) - w, -F(3, 4) - min(w, w + d))
    upper = min(F(1, 8) - w, F(3, 4) - max(w, w + d))
    return [lower, upper] if lower <= upper else []


out = []
for key, center in [
    ("perfect_separating_readout_positive_three_tenths", F(3, 10)),
    ("interior_common_action_failure", F(2, 5)),
]:
    row = DATA[key]
    worlds = [list(map(F, w)) for w in row["worlds"]]
    intervals = []
    for world in worlds:
        w, d, q = world
        if not (
            -2 <= w <= 2
            and -2 <= d <= 2
            and F(1, 5) <= q / d <= F(3, 10)
            and F(9, 10) <= w + d <= F(11, 10)
            and w + q == center
        ):
            raise ValueError("source binding failure")
        intervals.append(actions(world))
    if intervals != [list(map(F, a)) for a in row["individual_action_intervals"]]:
        raise ValueError("individual envelope")
    if not all(intervals) or max(a[0] for a in intervals) <= min(a[1] for a in intervals):
        raise ValueError("no common action not established")
    predictions = [w + q / 2 for w, d, q in worlds]
    baseline = [w + d for w, d, q in worlds]
    out.append(
        dict(
            diagnostic=key,
            center=str(center),
            individual_actions=[[str(x) for x in a] for a in intervals],
            baseline_pair_error_threshold=str(abs(baseline[0] - baseline[1]) / 2),
            heldout_pair_error_threshold=str(abs(predictions[0] - predictions[1]) / 2),
        )
    )
row = DATA["perfect_separating_readout_positive_three_tenths"]
mid = F(row["hypothetical_common_heldout_center"])
error = F(row["pair_discrimination_error_must_be_strictly_less_than"])
if not all(abs(F(p) - mid) == error for p in row["half_leakage_heldout_predictions"]):
    raise ValueError("strictness boundary")
(BASE / "critic_pairs_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
