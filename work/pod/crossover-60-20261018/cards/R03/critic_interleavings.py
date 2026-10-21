"""Exact diagnostic runtime interleavings; not a refinement proof of an executor."""

from dataclasses import dataclass, replace
from fractions import Fraction as F
from itertools import permutations
import json
from math import comb
from pathlib import Path

P = Path(__file__).resolve().parent


@dataclass(frozen=True)
class Snapshot:
    history: tuple
    task: str
    frame: str
    calibration: int
    version: int
    epoch: str


base = Snapshot((), "goalA", "world", 0, 0, "bootA")
proposal = base
# Enumerate single revision vs split check/write. Atomic compare-and-update is distinct.
rows = []
for order in permutations(["check", "write", "revision"]):
    if order.index("check") > order.index("write"):
        continue
    state = base
    ok = False
    stale = False
    for op in order:
        if op == "check":
            ok = state == proposal
        elif op == "revision":
            state = replace(state, task="goalB", version=state.version + 1)
        elif ok:
            stale = state != proposal
            state = replace(
                state, history=state.history + ("old-goal-event",), version=state.version + 1
            )
    rows.append({"order": order, "stale_accepted": stale})
assert sum(r["stale_accepted"] for r in rows) == 1
for order in permutations(["commit", "revision"]):
    state = base
    for op in order:
        if op == "revision":
            state = replace(state, task="goalB", version=state.version + 1)
        elif state == proposal:
            state = replace(state, history=("old-goal-event",), version=1)
    # Revision-before-commit cannot append the obsolete event.
    if order[0] == "revision":
        assert state.history == ()
# Read components across one atomic update: a snapshot which never existed.
new = replace(base, history=("new-history",), task="goalB", version=1)
torn = replace(base, task=new.task, version=new.version)
assert torn not in [base, new]
# Comparing only versions accepts a semantic mutation; full source equality rejects it.
mutations = [
    replace(base, history=("changed",)),
    replace(base, task="changed"),
    replace(base, frame="base"),
    replace(base, calibration=1),
]
assert all(s.version == base.version and s != base for s in mutations)
# ABA/restart distinctions: ordinary source append increments its unbounded Nat version.
changed = replace(base, task="goalB", version=1)
restored = replace(changed, task="goalA", version=2)
assert restored != base
reboot = replace(base, epoch="bootB")
assert reboot != base
assert (reboot.history, reboot.task, reboot.version) == (base.history, base.task, base.version)
# Two checks before either append: duplicate execution under split append, one under CAS.
state = base
checked = [state == base, state == base]
for ok in checked:
    if ok:
        state = replace(state, history=state.history + ("event",), version=state.version + 1)
assert state.history == ("event", "event")
state = base
for _ in range(2):
    if state == base:
        state = replace(state, history=state.history + ("event",), version=state.version + 1)
assert state.history == ("event",)
# A successful local CAS cannot itself give exactly-once actuator delivery.
network_delivery = ["event", "event"]
assert len(network_delivery) == 2
# Bounded clock error: independent-box sufficient gate vs invalid correlation assumption.
hc = F(100)
he = F(1001, 10)
D = F(1, 20)
eps = F(1, 5)
assert not hc + eps + D <= he - eps
for offset in [F(-1, 5), F(0), F(1, 5)]:
    assert hc - offset + D <= he - offset
# Same cancellation across independent domains is false: hat=t+offset.
c = hc - F(-1, 10)
e = he - F(1, 10)
assert hc + D <= he and c + D > e
# Using a stale pre-check clock can accept an already-missed start at atomic update.
check = F(1)
commit = F(6, 5)
execution = F(11, 10)
assert check + F(1, 100) <= execution and commit > execution


# Exact source four-box shape: interval ordering does not prove physical retiming fidelity.
def pos(t, tau, h, delta):
    return (
        delta
        * sum(F((-1) ** k * comb(4, k)) * max(t - tau - k * h, F(0)) ** 4 for k in range(5))
        / (24 * h**4)
    )


tau = F(1)
h = F(1, 5)
delta = F(1, 50)
eps = F(1, 1000)
t = tau - eps / 2
early = pos(t, tau - eps, h, delta)
nominal = pos(t, tau, h, delta)
assert early > 0 and nominal == 0
T = tau + 4 * h
late = pos(T, tau + eps, h, delta)
assert pos(T, tau, h, delta) == delta and late < delta
assert delta - late == delta * eps**4 / (24 * h**4)
assert F(1, 5) + eps + F(1, 100) <= tau - eps
out = {
    "split_interleavings": rows,
    "atomic_orders_checked": 2,
    "semantic_same_version_mutations": len(mutations),
    "torn_snapshot_not_live": True,
    "restart_epoch_distinguishes_reset": True,
    "duplicate_split_and_CAS": [2, 1],
    "common_offset_conservative_rejection": True,
    "independent_offset_false_accept": {"commit": str(c), "execution": str(e)},
    "stale_clock_false_accept": True,
    "retiming": {
        "tau": str(tau),
        "h": str(h),
        "delta": str(delta),
        "execution_error": str(eps),
        "early_observation": str(t),
        "early_new_prefix": str(early),
        "nominal_prefix": str(nominal),
        "deadline": str(T),
        "late_goal_gap": str(delta - late),
        "ordering_gate_still_passes": True,
    },
    "scope": "Synthetic runtime faults outside original atomic ideal-clock premises. Four-box position follows source formula, independently reconstructed. No existing source bug, actual scheduler, native atomicity, physical tracking or progress proof.",
}
(P / "critic_interleavings.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
