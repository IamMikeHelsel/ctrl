"""Independent exhaustive finite event-word audit of PM transport fixture."""

import json
from itertools import permutations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent
count = failures = max_queue = 0
for delays in product(range(3), repeat=5):
    arrival = tuple(2 * i + delays[i] for i in range(5))
    times = sorted(set(arrival))
    possibilities = [list(permutations(i for i in range(5) if arrival[i] == t)) for t in times]
    for batches in product(*possibilities):
        word = tuple(i for batch in batches for i in batch)
        for bits in product((False, True), repeat=5):
            first = next((i for i in range(5) if bits[i]), None)
            record_highs = [i for j, i in enumerate(word) if not word[:j] or i > max(word[:j])]
            naive = next((i for i in record_highs if bits[i]), None)
            # Per-index release requires the actual packet by its deadline.
            certified = []
            for i in range(5):
                assert arrival[i] <= 2 * i + 2
                assert all(arrival[j] <= 2 * i + 2 for j in range(i + 1))
                certified.append(bits[i])
            released_first = next((i for i, g in enumerate(certified) if g), None)
            assert released_first == first
            failures += naive != first
            count += 1
        # Queue just after receiving a batch, before releases at that instant.
        for t in set(arrival) | {2 * i + 2 for i in range(5)}:
            size = sum(arrival[i] <= t <= 2 * i + 2 for i in range(5))
            max_queue = max(max_queue, size)
saved = json.loads((HERE / "pm_protocol.json").read_text())
assert (count, failures, max_queue) == (
    saved["traces"],
    saved["latest_only_failures"],
    saved["max_pending_payloads"],
)
result = {
    "traces": count,
    "latest_only_failures": failures,
    "max_queue": max_queue,
    "ordered_release_failures": 0,
    "scope": "Independent finite combinatorial audit, trusted same-origin Boolean payloads and complete delivery, not a physical or general network implementation proof.",
}
(HERE / "critic_delivery.json").write_text(json.dumps(result, indent=2) + "\n")
print(result)
