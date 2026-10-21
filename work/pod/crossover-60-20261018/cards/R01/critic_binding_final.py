"""Independent final-wrapper replay, retaining the issue-time composition gap."""

import hashlib
import json
import runpy
import sys
from dataclasses import replace
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).parent
sys.path.insert(0, str(P))
m = runpy.run_path(str(P / "pm_binding.py"), run_name="critic_final")
C, E, S, bound = [m[k] for k in ["Commit", "Event", "State", "bound_append"]]
c = C(1, 1, F(1, 1000), F(3, 2), F(1, 5), (), E(F(11, 50), F(1, 1000)))
r = (1, 1, c.goal, c.deadline, c.h)
s, status = bound(S(), c, r, F(1, 5))
assert status == "appended"
assert bound(s, c, r, F(2)) == (s, "duplicate")
for delta, expected in [
    (F(3, 100), "appended"),
    (F(31, 1000), "jerk_contract_rejected"),
    (F(1, 25), "jerk_contract_rejected"),
]:
    altered = replace(c, goal=delta, event=replace(c.event, delta=delta))
    assert bound(S(), altered, (1, 1, delta, c.deadline, c.h), F(1, 5))[1] == expected
for bad_h in [F(0), F(-1), F(1, 10)]:
    altered = replace(c, h=bad_h)
    assert (
        bound(S(), altered, (1, 1, c.goal, c.deadline, bad_h), F(1, 5))[1]
        == "jerk_contract_rejected"
    )
# Late conflicting payload remains conflict, never duplicate or second effect.
conflict = replace(c, event=replace(c.event, time=F(23, 100)))
assert bound(s, conflict, r, F(2)) == (s, "conflict")
# Receipt and time protections still operate for fresh requests.
forged = replace(c, goal=F(2, 1000), event=replace(c.event, delta=F(2, 1000)))
assert bound(S(), forged, r, F(1, 5))[1] == "authority_binding_rejected"
assert bound(S(), c, r, F(2))[1] == "causality_rejected"
next_c = C(1, 2, F(2, 1000), F(3), F(1, 5), s.history, E(F(3, 2), F(1, 1000)))
assert bound(s, next_c, (1, 2, next_c.goal, next_c.deadline, next_c.h), F(1, 2))[1] == "appended"
assert F(1, 2) < c.event.time + 4 * c.h
out = {
    "source_sha256": hashlib.sha256((P / "pm_binding.py").read_bytes()).hexdigest(),
    "late_retry": "duplicate",
    "late_conflict": "conflict",
    "30mm": "accepted",
    "31mm_and_40mm": "jerk_rejected",
    "three_invalid_widths": "rejected",
    "issue_before_old_tail_complete": "still accepted; original isolated theorem premise missing",
    "scope": "Final static binding replay, not old executable guard or physical/task theorem refinement.",
}
(P / "critic_binding_final_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
