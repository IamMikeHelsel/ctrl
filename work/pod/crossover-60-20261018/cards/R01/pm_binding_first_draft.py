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
        "scope": "Five exact interface tests. Supplied receipt truth, common physical clock and durable atomic append are assumptions. No network, scheduler, physical task completion or integrated implementation.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
