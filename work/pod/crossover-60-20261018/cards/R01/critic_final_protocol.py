"""Independent monitors for producer protocol transitions and semantic certificates."""

import hashlib
import itertools
import json
import runpy
from pathlib import Path

P = Path(__file__).parent
domain = runpy.run_path(str(P / "domain_protocol.py"), run_name="critic_import")
Packet, Receiver, step = [domain[k] for k in ["Packet", "Receiver", "step"]]
alphabet = [
    Packet("observe", goal_um=1000),
    Packet("revise", version=1, goal_um=1000),
    Packet("revise", version=1, goal_um=-1000),
    Packet("revise", version=2, goal_um=0),
    Packet("revise", session=0, version=3, goal_um=-1000),
    Packet("oracle_complete_tail"),
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
            assert all(task in prior_commits for task in state.reference_tails_done)
            if packet.kind == "observe":
                assert state == old
        count += 1
assert count == 9331 and transitions == 44790

for kind in ["cancel", "complete", "bogus"]:
    try:
        step(Receiver(), Packet(kind, version=1, goal_um=999))
    except ValueError:
        pass
    else:
        raise AssertionError("Unknown kind accepted")

out = {
    "traces": count,
    "transitions": transitions,
    "unknown_kinds_rejected": 3,
    "source_sha256": hashlib.sha256((P / "domain_protocol.py").read_bytes()).hexdigest(),
    "scope": "Final finite model independently replayed; internal oracle semantics assumed, not runtime verified",
}
(P / "critic_final_protocol_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
