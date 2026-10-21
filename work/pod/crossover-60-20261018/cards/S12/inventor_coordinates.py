"""Decision-coordinate abstraction: exact for frozen action predicate, not updates."""

import json
from fractions import Fraction as F
from pathlib import Path

from inventor_exact import actions, enc, separated

points = separated["1"]
c = F(-1, 2)
wlo, whi = min(p[0] for p in points), max(p[0] for p in points)
dlo, dhi = min(p[1] for p in points), max(p[1] for p in points)
blo, bhi = min(p[0] + p[1] for p in points), max(p[0] + p[1] for p in points)
# Independent-source box forgets negative correlation between w and d.
source_box_upper = whi + dhi + c
assert source_box_upper == F(449, 560) > F(3, 4)
# Decision-coordinate box retains exactly the only queried supports.
endpoint_upper = max(whi, bhi) + c
endpoint_lower = min(wlo, blo) + c
wheel_upper = whi + c
wheel_lower = wlo + c
assert endpoint_upper == F(3, 5) <= F(3, 4)
assert endpoint_lower >= -F(3, 4)
assert wheel_upper <= F(1, 8) and wheel_lower >= -F(1, 8)
# The equality is general: w+c+rho*d=(1-rho)*(w+c)+rho*(b+c).
# Triangle inequality gives sufficiency of endpoint bounds, while rho=0,1
# proves necessity; no independence assumption or convexity of worlds required.
lo = max(-F(1, 8) - wlo, -F(3, 4) - min(wlo, blo))
hi = min(F(1, 8) - whi, F(3, 4) - max(whi, bhi))
assert [lo, hi] == actions(separated)["safe_interval"]
result = {
    "original_model_unchanged": True,
    "nonempty_guard_required": True,
    "source_coordinates_box": {"w": [wlo, whi], "d": [dlo, dhi]},
    "source_box_mixed_upper_for_original_action": source_box_upper,
    "source_box_false_reject": True,
    "decision_coordinates_box": {"w": [wlo, whi], "b=w+d": [blo, bhi]},
    "decision_box_mixed_range_for_original_action": [endpoint_lower, endpoint_upper],
    "decision_box_exact_safe_action_interval": [lo, hi],
    "derivation": "For every nonempty joint world set, max over rho in [0,1] of |w+c+rho*d| equals max(|w+c|,|w+d+c|). Thus four exact supports suffice for this predicate, regardless of source identifiability.",
    "boundary": "Discarded q and dependencies must remain available for joint observation consistency and future updates; this is a decision summary only, not a replacement belief state.",
    "evidence": "Exact rational fixture and elementary algebra; not Lean or robot validation.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(enc(result), indent=2) + "\n")
print(json.dumps(enc(result), indent=2))
