"""Exact finite reference-history append certificate, not a plant or network model."""

import json
from dataclasses import dataclass, replace
from fractions import Fraction as F
from pathlib import Path


@dataclass(frozen=True)
class Event:
    time: F
    delta: F


@dataclass(frozen=True)
class Commit:
    session: int
    revision: int
    goal: F
    deadline: F
    h: F
    prior: tuple[Event, ...]
    event: Event


@dataclass(frozen=True)
class State:
    history: tuple[Event, ...] = ()
    receipts: tuple[Commit, ...] = ()


def final_goal(history):
    return sum((e.delta for e in history), F(0))


def append(state, c):
    # Session/authority installation is trusted externally; no truth inference.
    if c.session != 1:
        return state, "session_rejected"
    prior_receipt = next((r for r in state.receipts if r.revision == c.revision), None)
    if prior_receipt is not None:
        return state, "duplicate" if prior_receipt == c else "conflict"
    if c.revision <= max((r.revision for r in state.receipts), default=0):
        return state, "stale"
    if c.prior != state.history:
        return state, "prefix_rejected"
    if c.h != F(1, 5):
        return state, "plant_contract_rejected"
    if c.event.delta != c.goal - final_goal(c.prior):
        return state, "goal_binding_rejected"
    # Isolated event only; complete old reference tail before new execution.
    if c.event.time < max((e.time + 4 * c.h for e in c.prior), default=F(0)):
        return state, "tail_rejected"
    if c.deadline < c.event.time + 4 * c.h:
        return state, "deadline_rejected"
    new = State((*state.history, c.event), (*state.receipts, c))
    assert final_goal(new.history) == c.goal
    return new, "appended"


def main():
    c = Commit(1, 1, F(1, 1000), F(3, 2), F(1, 5), (), Event(F(11, 50), F(1, 1000)))
    s, status = append(State(), c)
    assert status == "appended"
    checks = [("first", status)]
    mutations = [
        ("replay", c, "duplicate"),
        ("changed_time_same_key", replace(c, event=replace(c.event, time=F(23, 100))), "conflict"),
        ("changed_goal_same_key", replace(c, goal=F(2, 1000)), "conflict"),
        ("changed_deadline_same_key", replace(c, deadline=F(2)), "conflict"),
        ("stale_prefix_new_revision", replace(c, revision=2), "prefix_rejected"),
        ("old_session", replace(c, session=0), "session_rejected"),
    ]
    for name, m, expected in mutations:
        new, status = append(s, m)
        assert status == expected and new == s
        checks.append((name, status))
    next_c = Commit(1, 2, F(2, 1000), F(3), F(1, 5), s.history, Event(F(3, 2), F(1, 1000)))
    for name, m, expected in [
        (
            "wrong_delta",
            replace(next_c, event=replace(next_c.event, delta=F(2, 1000))),
            "goal_binding_rejected",
        ),
        (
            "pending_tail",
            replace(next_c, event=replace(next_c.event, time=F(1, 2))),
            "tail_rejected",
        ),
        ("impossible_deadline", replace(next_c, deadline=F(2)), "deadline_rejected"),
        ("changed_width", replace(next_c, h=F(1, 10)), "plant_contract_rejected"),
    ]:
        new, status = append(s, m)
        assert status == expected and new == s
        checks.append((name, status))
    s2, status = append(s, next_c)
    assert status == "appended" and final_goal(s2.history) == F(2, 1000)
    # Receipt loss alone still rejects stale prefix. Losing both receipt and
    # actual-history evidence after restart defeats this model's replay fence.
    lost_receipt = replace(s, receipts=())
    assert append(lost_receipt, c)[1] == "prefix_rejected"
    assert append(State(), c)[1] == "appended"
    # Compiling absolute request again against current goal yields delta0.
    # The dangerous case is replay of a previously compiled nonzero increment.
    recomputed_delta = c.goal - final_goal(s.history)
    assert recomputed_delta == 0
    naive_history = (*s.history, Event(F(23, 100), c.event.delta))
    naive_final = final_goal(naive_history)
    jerk_sum = 2 * sum(abs(e.delta) for e in naive_history) / c.h**3
    radius = F(1, 5000)
    minimum_goal_error = abs(naive_final - c.goal) - radius
    assert jerk_sum == F(1, 2) < F(15, 2)
    assert minimum_goal_error == F(1, 1250) > radius
    report = {
        "checks": checks,
        "successful_successor": status,
        "safe_history_final": str(final_goal(s2.history)),
        "naive_duplicate_final": str(naive_final),
        "naive_jerk_upper_bound": str(jerk_sum),
        "minimum_goal_error_under_existing_tube": str(minimum_goal_error),
        "absolute_request_recompiled_delta": str(recomputed_delta),
        "scope": "Trusted session and atomic receiver; exact history equality, no hash/collision assumption. Static admission relation only: no current-clock check, authentication, delivery, actual tail completion, plant execution, or Python-to-Lean refinement. Rejected request is not task success.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
