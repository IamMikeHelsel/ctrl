"""Independent minimal tie-order analysis: storage is not free scheduling."""

import json
from itertools import permutations
from pathlib import Path

rows = []
for events in permutations(("receive_due", "receive_future", "commit_due")):
    inbox = set()
    maximum = 0
    committed = False
    valid = True
    for event in events:
        if event == "receive_due":
            inbox.add(632)
        elif event == "receive_future":
            inbox.add(633)
        elif 632 in inbox:
            inbox.remove(632)
            committed = True
        else:
            valid = False
        maximum = max(maximum, len(inbox))
    rows.append(
        {
            "events": events,
            "valid_due_before_commit": valid,
            "committed_due": committed,
            "max_application_packets": maximum,
            "remaining": sorted(inbox),
        }
    )
legal = [x for x in rows if x["valid_due_before_commit"]]
assert len(legal) == 3
assert all(x["committed_due"] and x["remaining"] == [633] for x in legal)
assert sum(x["max_application_packets"] == 1 for x in legal) == 1
assert sum(x["max_application_packets"] == 2 for x in legal) == 2
result = {
    "scope": "All six logical orderings of one due receipt, one future receipt, and due commit at a tied real instant. No physical execution-time assertion.",
    "rows": rows,
    "conclusion": "Three orderings respect due-before-commit. One uses one application payload slot; two need two. Selecting the first ordering requires receive scheduling or an externally retained future packet. This does not reduce total physical buffering.",
    "source_fixture": "Actual source first632 and nonqualifying633; packet identities must remain separate.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
