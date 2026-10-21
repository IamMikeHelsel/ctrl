"""Independent monitors for producer protocol transitions and semantic certificates."""

import itertools
import json
import runpy
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).parent
domain = runpy.run_path(str(P / "critic_protocol_snapshot.py.snapshot"), run_name="critic_import")
Packet, Receiver, step = [domain[k] for k in ["Packet", "Receiver", "step"]]
alphabet = [
    Packet("observe", goal_um=1000),
    Packet("revise", version=1, goal_um=1000),
    Packet("revise", version=1, goal_um=-1000),
    Packet("revise", version=2, goal_um=0),
    Packet("revise", session=0, version=3, goal_um=-1000),
    Packet("complete"),
]
count = transitions = 0
for size in range(6):
    for trace in itertools.product(alphabet, repeat=size):
        state = Receiver()
        prior_commits = []
        for packet in trace:
            old = state
            state, status = step(old, packet)
            transitions += 1
            assert state.high >= old.high
            if status == "accepted":
                assert not old.busy and packet.session == 1 and packet.version > old.high
                prior_commits.append((packet.version, packet.goal_um))
            else:
                assert state.committed == old.committed
            assert list(state.accepted) == prior_commits
            assert all(task in prior_commits for task in state.completed)
            if packet.kind == "observe":
                assert state == old
        count += 1
assert count == 9331 and transitions == 44790
# Boundary probes outside the six-token alphabet, recorded rather than assumed fixed.
s, _ = step(Receiver(), Packet("revise", version=1, goal_um=1000))
s, _ = step(s, Packet("complete"))
s, _ = step(s, Packet("revise", version=2, goal_um=2000))
stale_complete, status = step(s, Packet("complete", session=0, version=1))
unknown, status_unknown = step(Receiver(), Packet("cancel", version=1, goal_um=999))

# Independent geometric interpretation of the inventor's semantic encoding counts.
src = json.loads((P / "inventor_information.json").read_text())
goals = [F(x) for x in src["finite_semantic_example"]["goals"]]
eps = F(src["original_tolerances"]["task_epsilon"])
counts = {}
for n in [1, 2, 3]:
    valid = 0
    for labels in itertools.product(range(n), repeat=len(goals)):
        okay = True
        for label in set(labels):
            selected = [g for g, l in zip(goals, labels, strict=True) if l == label]
            okay &= max(g - eps for g in selected) <= min(g + eps for g in selected)
        valid += okay
    counts[n] = valid
assert counts == {1: 0, 2: 0, 3: 6}
assert (
    counts[2] == src["finite_semantic_example"]["binary_encodings_that_satisfy_all_position_bands"]
)
assert counts[3] == src["finite_semantic_example"]["three_symbol_valid_encodings"]


# Exhaustive bounded one-bit correction packing: all labels need distance>=3.
def distance(a, b):
    return (a ^ b).bit_count()


minimal = None
for n in range(1, 6):
    exists = any(
        all(distance(a, b) >= 3 for a, b in itertools.combinations(code, 2))
        for code in itertools.combinations(range(2**n), 3)
    )
    if exists:
        minimal = n
        break
assert minimal == 5
code = [int(c, 2) for c in src["optional_command_bit_error_model"]["codebook"]]
assert all(distance(a, b) >= 3 for a, b in itertools.combinations(code, 2))
for i, c in enumerate(code):
    for received in [c] + [c ^ (1 << j) for j in range(5)]:
        assert [k for k, w in enumerate(code) if distance(received, w) <= 1] == [i]
# Quantization witness is a tube-allowed realization, not a claimed ODE trajectory.
assert abs(F(4, 5) - F(1001, 1000)) == F(201, 1000) > eps
# Mutation controls: independently checked code spheres must remain disjoint;
# reported interval and finite counts must remain bound to exact recomputation.
corrupted_code = [code[0], code[0] ^ 1, code[2]]
assert not all(distance(a, b) >= 3 for a, b in itertools.combinations(corrupted_code, 2))
assert F("1/5") != abs(F(4, 5) - F(1001, 1000))
assert counts[2] != 1
result = {
    "certificate_mutations_rejected": 3,
    "traces": count,
    "transitions": transitions,
    "encoding_counts": counts,
    "one_bit_correction_minimum_length": minimal,
    "stale_complete_clears_busy": s.busy and not stale_complete.busy,
    "unknown_kind_status": status_unknown,
    "unknown_kind_committed_goal": unknown.committed[1],
    "scope": "Independent finite monitors and certificate checks. Completion oracle assumptions remain external; no delivery, plant or deadline theorem.",
}
(P / "critic_replay_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
