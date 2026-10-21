"""Declared finite sideband protocol fault witnesses, not a deployed implementation."""

import json
from dataclasses import asdict, dataclass
from pathlib import Path

P = Path(__file__).parent


@dataclass(frozen=True)
class Revision:
    session: str
    epoch: int
    goal_mm: int
    deadline_tick: int
    expected_previous_epoch: int


def guarded_commit(state, proposal):
    """Single atomic transition; physical feasibility is deliberately not claimed."""
    session, epoch, goal = state
    if proposal.session != session:
        return state, "wrong session"
    if proposal.expected_previous_epoch != epoch:
        return state, "stale predecessor"
    if proposal.epoch <= epoch:
        return state, "non-increasing epoch"
    return (session, proposal.epoch, proposal.goal_mm), "committed"


initial = ("run-A", 0, 0)
move = Revision("run-A", 1, 1, 10, 0)
accepted, result = guarded_commit(initial, move)
assert result == "committed" and accepted[2] == 1
# A delayed old-session packet with a larger integer epoch cannot revive after reset.
old = Revision("run-A", 100, 20, 10, 0)
new_session = ("run-B", 0, 0)
assert old.epoch > new_session[1]
assert guarded_commit(new_session, old)[0] == new_session
# Two requests prepared against the same predecessor cannot both commit.
other = Revision("run-A", 2, -1, 10, 0)
assert guarded_commit(accepted, other)[1] == "stale predecessor"
# Numeric epoch equality does not establish duplicate identity.
conflict = Revision("run-A", 1, -1, 10, 0)
assert conflict.epoch == move.epoch and conflict != move
# A naive same-epoch ACK would assert success for two different goal payloads.
naive_ack = conflict.epoch == accepted[1]
assert naive_ack and conflict.goal_mm != accepted[2]

# A receiver cannot make an undelivered cancellation affect its present trajectory.
# Both worlds contain the same queued move through tick5; cancellation only arrives6.
queue = [(5, 1)]
received_before_execution = []
assert not received_before_execution
position_at_5 = queue[0][1]
assert position_at_5 != 0
# Cancellation authority issued at4 cannot imply instant hold at0 if unknown until6.

# Even a timely cancellation cannot erase already executed physical displacement.
executed_position = 1
logical_goal_after_cancel = 0
assert executed_position != logical_goal_after_cancel
# A verified replacement/stop plan would be an additional plant-dependent obligation.

# Absolute deadlines without bounded clock offset can pass locally and fail truly.
actual_now = 10
clock_offset = -3
local_now = actual_now + clock_offset
deadline = 9
assert local_now <= deadline < actual_now

# Receipt/admission is not a certificate of delivery to the actuator or completion.
receipt_ack, actuator_delivery, completed = True, False, False
assert receipt_ack and not actuator_delivery and not completed

# Rejecting a physically infeasible request preserves a safe incumbent, but fails task.
incumbent_safe, accepted_move, fulfilled_move = True, False, False
assert incumbent_safe and not accepted_move and not fulfilled_move

result = {
    "model": "Synthetic single-receiver atomic version check; no scheduler, network or plant proof",
    "accepted_revision": asdict(move),
    "failure_cases": [
        "old session with larger epoch",
        "stale concurrent predecessor",
        "same epoch with different payload",
        "undelivered cancellation before queued execution",
        "logical cancellation after physical motion",
        "unknown clock offset makes deadline check false",
        "receipt acknowledgement with no actuator delivery",
        "safe rejection incorrectly counted as task success",
    ],
    "unverified_assumptions": [
        "trusted authorized task source and truthful task metadata",
        "persistent session/epoch allocation and atomic commit",
        "task-specific allowed transition set and physical feasibility",
        "bounded delivery, queueing, clock mapping and execution latency",
        "cancellation effect specification; cancellation cannot retroactively undo motion",
    ],
}
(P / "critic_protocol_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
