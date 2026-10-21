"""Protocol/reference traces, not a plant or hardware implementation."""

import json
from fractions import Fraction as F
from math import comb
from pathlib import Path


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, list):
        return [encode(v) for v in x]
    if isinstance(x, tuple):
        return [encode(v) for v in x]
    if isinstance(x, dict):
        return {str(k): encode(v) for k, v in x.items()}
    return x


def primitive(z):
    return sum(F((-1) ** i * comb(4, i), 24) * max(z - i, 0) ** 4 for i in range(5))


def third_primitive(z):
    return sum((-1) ** i * comb(4, i) * max(z - i, 0) for i in range(5))


h, radius, deadline = F(1, 5), F(1, 5), F(3, 2)
assert primitive(F(0)) == 0 and primitive(F(1)) == F(1, 24)
assert primitive(F(2)) == F(1, 2) and primitive(F(4)) == 1


def reference(t, events):
    return sum(delta * primitive((t - start) / h) for start, delta in events)


# Replaying an already compiled displacement is a task-semantic fault even if
# the sum-of-jerk-bounds still satisfies the unchanged reference guard budget.
original = [(F(11, 50), F(1))]
replayed = original + [(F(23, 100), F(1))]
assert reference(deadline, original) == 1
assert reference(deadline, replayed) == 2
jerk_bound_m = sum(2 * abs(delta) / 1000 / h**3 for _, delta in replayed)
assert jerk_bound_m == F(1, 2) < F(15, 2)
knots = sorted({start + i * h for start, _ in replayed for i in range(5)})
jerk_knots = [
    [t, sum(delta / 1000 / h**3 * third_primitive((t - start) / h) for start, delta in replayed)]
    for t in knots
]
exact_peak_jerk = max(abs(value) for _, value in jerk_knots)
assert exact_peak_jerk == F(77, 160) < F(15, 2)
minimum_goal_error = abs(reference(deadline, replayed) - 1) - radius
assert minimum_goal_error == F(4, 5) > radius

# A reducer demonstrating the identity/order obligations, not verifying
# scheduling, clocks, authentication or a physical plant.
state = {"epoch": 6, "goal": F(0), "seen": {}, "events": [], "log": []}


def receive(kind, epoch=None, goal=None, now=None, execution=None):
    if kind == "OBSERVE":
        state["log"].append("ADVISORY_ONLY")
        return
    payload = (goal, deadline, execution)
    if epoch in state["seen"]:
        status = "DUPLICATE_ACK" if state["seen"][epoch] == payload else "CONFLICT_REJECT"
    elif epoch <= state["epoch"]:
        status = "STALE_REJECT"
    elif any(start + 4 * h > now for start, _ in state["events"]):
        status = "FAILED_REQUEST_PENDING_OLD_TAIL"
    elif now > execution or execution + 4 * h > deadline:
        status = "FAILED_REQUEST_TIMING"
    else:
        delta = goal - state["goal"]
        state["events"].append((execution, delta))
        state["goal"], state["epoch"] = goal, epoch
        state["seen"][epoch] = payload
        status = "ADMITTED"
    state["log"].append(status)


receive("REVISE", 7, F(1), F(11, 50), F(11, 50))
receive("OBSERVE", goal=F(1))
receive("REVISE", 7, F(1), F(23, 100), F(11, 50))
receive("REVISE", 7, F(1, 2), F(24, 100), F(11, 50))
receive("REVISE", 6, F(0), F(3, 10), F(3, 10))
receive("REVISE", 8, F(0), F(3, 10), F(3, 10))
assert state["log"] == [
    "ADMITTED",
    "ADVISORY_ONLY",
    "DUPLICATE_ACK",
    "CONFLICT_REJECT",
    "STALE_REJECT",
    "FAILED_REQUEST_PENDING_OLD_TAIL",
]
assert state["events"] == original and state["goal"] == 1
# The last rejected request is a failed new task, not a successful hold.

# Original fixed20mm event, unchanged h and deadline. A delayed executiontime
# violates the source timing premise; copied intent cannot repair that latency.
nominal20 = [(F(11, 50), F(20))]
late20 = [(F(13, 10), F(20))]
checktime = F(51, 50)
assert reference(checktime, nominal20) == 20
assert reference(checktime, late20) == 0
assert reference(deadline, late20) == F(5, 6)
late_minerror = 20 - reference(deadline, late20) - radius
assert late_minerror == F(569, 30) > radius

# Exactness of goal representation under a full symmetric tracking tube.
# For any nonzero offset, choosing the same-sign extremal error gives |offset|+R.
for offset in [F(-1), F(-1, 1000), F(0), F(1, 1000), F(1)]:
    extreme = radius if offset >= 0 else -radius
    assert abs(offset + extreme) == abs(offset) + radius
    assert (abs(offset + extreme) <= radius) == (offset == 0)

result = {
    "model_scope": "Reference primitive and semantic reducer only; no integration or new plant run.",
    "duplicate_displacement_failure": {
        "events": replayed,
        "reference_at_deadline_mm": reference(deadline, replayed),
        "summed_jerk_bound_m_per_s3": jerk_bound_m,
        "piecewise_linear_jerk_knots": jerk_knots,
        "exact_peak_reference_jerk_m_per_s3": exact_peak_jerk,
        "unchanged_guard_limit_m_per_s3": F(15, 2),
        "minimum_goal_error_if_original_tracking_tube_holds_mm": minimum_goal_error,
        "meaning": "Dynamically admissible reference generation can still implement the wrong task after duplicate execution. Exact reference jerk verified at every knot; no existing guard implementation or plant run is claimed.",
    },
    "idempotent_epoch_reducer": state,
    "late_execution_copy": {
        "fixed_goal_mm": 20,
        "deadline": deadline,
        "nominal_execution": F(11, 50),
        "actual_execution": F(13, 10),
        "reference_predictions_at_1_02s": [F(20), F(0)],
        "actual_reference_at_deadline_mm": F(5, 6),
        "minimum_goal_error_under_tracking_tube_mm": late_minerror,
        "meaning": "An intent-copy predictor using issue/nominal time instead of actual admitted execution predicts movement that has not occurred. This scenario violates the source delay bound; it is not a counterexample to its theorem.",
    },
    "robust_reference_exactness": "For every e in[-R,R],|q+e-g|<=R implies q=g: e=R gives q<=g and e=-R gives q>=g. Conversely q=g suffices. This is necessary relative to the interval abstraction, not proof that the physical plant reaches both extrema.",
    "limits": [
        "Correct authoritative labels remain external assumptions.",
        "Generation/session handling, restart persistence, cryptographic authentication and clocks are not implemented.",
        "New requests during a pending tail are explicitly failed, not claimed complete.",
        "An actual executed-command ledger estimates state but cannot reveal unissued or mislabeled intent.",
    ],
}
Path(__file__).with_suffix(".json").write_text(json.dumps(encode(result), indent=2) + "\n")
print(json.dumps(encode(result), indent=2))
