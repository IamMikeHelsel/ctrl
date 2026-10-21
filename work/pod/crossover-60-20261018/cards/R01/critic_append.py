"""Independent finite review of the static append relation, no producer main/checker."""

import json
import runpy
from dataclasses import replace
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).parent
m = runpy.run_path(str(P / "pm_append.py"), run_name="critic_import")
State, Event, Commit, append = [m[k] for k in ["State", "Event", "Commit", "append"]]
c = Commit(1, 1, F(1, 1000), F(3, 2), F(1, 5), (), Event(F(11, 50), F(1, 1000)))
s, status = append(State(), c)
assert status == "appended" and s.history == (c.event,)
second = Commit(1, 2, F(2, 1000), F(3), F(1, 5), s.history, Event(F(3, 2), F(1, 1000)))
cases = [
    (c, "duplicate"),
    (replace(c, deadline=F(3)), "conflict"),
    (replace(c, goal=F(2, 1000)), "conflict"),
    (replace(c, event=Event(F(23, 100), F(1, 1000))), "conflict"),
    (replace(c, revision=2), "prefix_rejected"),
    (replace(c, session=0), "session_rejected"),
    (replace(second, event=Event(F(3, 2), F(2, 1000))), "goal_binding_rejected"),
    (replace(second, event=Event(F(1, 2), F(1, 1000))), "tail_rejected"),
    (replace(second, deadline=F(2)), "deadline_rejected"),
    (replace(second, h=F(1, 10)), "plant_contract_rejected"),
]
for packet, wanted in cases:
    new, status = append(s, packet)
    assert new == s and status == wanted
s2, status = append(s, second)
assert status == "appended" and sum(e.delta for e in s2.history) == second.goal
# An externally supplied request identity is not encoded: a wholly self-consistent
# changed request is accepted. This is a documented authority premise, not a bug.
forged = replace(c, goal=F(9), event=replace(c.event, delta=F(9)))
assert append(State(), forged)[1] == "appended"
# No current clock enters the relation; static event times may be in the past.
actual_now = F(10)
assert c.event.time < actual_now and append(State(), c)[1] == "appended"
# Recovery with history but missing receipts rejects the old prefix.
assert append(replace(s, receipts=()), c)[1] == "prefix_rejected"
assert append(State(), c)[1] == "appended"
# Fixed width and exact history are required, not mutable interpretation metadata.
assert append(s, replace(second, h=F(2, 5)))[1] == "plant_contract_rejected"
assert F(2, 1000) - F(1, 1000) - F(1, 5000) == F(1, 1250)
out = {
    "first_and_successor": "passed",
    "negative_append_cases": len(cases),
    "tube_error_lower_m": "1/1250",
    "self_consistent_changed_authority_request_accepted": True,
    "past_event_without_clock_accepted": True,
    "limits": "Static relation only, externally trusted authority and validated current state. No jerk guard, physical dynamics, receipt durability, current clock or authentication verification.",
}
(P / "critic_append_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
