"""Bind a static append certificate to a supplied authoritative receipt and time.

Receipt truth and a valid common physical clock are explicit external assumptions.
"""

import json
from dataclasses import replace
from fractions import Fraction as F
from pathlib import Path

from pm_append import Commit, Event, State, append


def bound_append(state, c, receipt, admission_time):
    # Receipt must originate from task authority, not the certificate producer.
    if (c.session, c.revision, c.goal, c.deadline, c.h) != receipt:
        return state, "authority_binding_rejected"
    if any(r.revision == c.revision for r in state.receipts):
        return append(state, c)
    if c.h != F(1, 5) or 2 * abs(c.event.delta) / c.h**3 > F(15, 2):
        return state, "jerk_contract_rejected"
    if c.event.time < admission_time:
        return state, "causality_rejected"
    return append(state, c)


def main():
    c = Commit(1, 1, F(1, 1000), F(3, 2), F(1, 5), (), Event(F(11, 50), F(1, 1000)))
    receipt = (1, 1, F(1, 1000), F(3, 2), F(1, 5))
    forged = replace(c, goal=F(2, 1000), event=replace(c.event, delta=F(2, 1000)))
    # Self-consistency is not external task binding.
    assert append(State(), forged)[1] == "appended"
    assert bound_append(State(), forged, receipt, F(1, 5))[1] == "authority_binding_rejected"
    assert bound_append(State(), c, receipt, F(2))[1] == "causality_rejected"
    assert bound_append(State(), c, receipt, F(1, 5))[1] == "appended"
    accepted, _ = bound_append(State(), c, receipt, F(1, 5))
    assert bound_append(accepted, c, receipt, F(2))[1] == "duplicate"
    large = replace(c, goal=F(1, 25), event=replace(c.event, delta=F(1, 25)))
    large_receipt = (1, 1, F(1, 25), F(3, 2), F(1, 5))
    assert bound_append(State(), large, large_receipt, F(1, 5))[1] == "jerk_contract_rejected"
    # Copying forged content into the receipt defeats this check: no inference
    # of intent, authentication or authority truth is being claimed.
    bad_receipt = (1, 1, F(2, 1000), F(3, 2), F(1, 5))
    assert bound_append(State(), forged, bad_receipt, F(1, 5))[1] == "appended"
    out = {
        "self_consistent_wrong_goal_without_receipt": "accepted",
        "wrong_goal_with_true_receipt": "rejected",
        "past_execution_at_admission": "rejected",
        "correct_receipt_and_causal_time": "accepted",
        "false_receipt": "still trusted; not detected",
        "late_identical_retry": "duplicate receipt; no second effect",
        "authorized40mm_move": "rejected: isolated jerk10 exceeds7.5",
        "scope": "Seven exact interface tests. Supplied receipt truth, common physical clock and durable atomic append are assumptions. Conservative isolated jerk check is separate from the original executable guard; issue-time completed-tail premise still missing. No network, scheduler, physical task completion or integrated implementation.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
