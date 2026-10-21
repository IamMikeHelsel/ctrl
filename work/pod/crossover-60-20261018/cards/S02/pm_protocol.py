"""Finite exhaustive delivery-order experiment; no plant safety theorem."""

import json
from itertools import permutations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent
N = 5
traces = 0
naive_failures = 0
max_queue = 0
first_failure = None
for delays in product(range(3), repeat=N):
    arrivals = [2 * i + delays[i] for i in range(N)]
    times = sorted(set(arrivals) | {2 * i + 2 for i in range(N)})
    batches = [[i for i in range(N) if arrivals[i] == t] for t in times]
    orders = [tuple(permutations(batch)) for batch in batches]
    for delivery_order in product(*orders):
        for guard in product((False, True), repeat=N):
            target = next((i for i in range(N) if guard[i]), None)
            queue = {}
            chosen = None
            latest = -1
            naive = None
            frontier = 0
            for t, batch in zip(times, delivery_order, strict=True):
                for i in batch:
                    queue[i] = guard[i]
                    max_queue = max(max_queue, len(queue))
                    if i > latest:
                        latest = i
                        if naive is None and guard[i]:
                            naive = i
                if t >= 2 and t % 2 == 0 and t // 2 - 1 < N:
                    due = t // 2 - 1
                    assert due == frontier and due in queue
                    payload = queue.pop(due)
                    if chosen is None and payload:
                        chosen = due
                    frontier += 1
            assert chosen == target and frontier == N and not queue
            traces += 1
            if naive != target:
                naive_failures += 1
                if first_failure is None:
                    first_failure = {
                        "delays_ticks": delays,
                        "guard": guard,
                        "batches": delivery_order,
                        "target": target,
                        "naive": naive,
                    }
assert max_queue == 2
result = {
    "messages": N,
    "tick_seconds": "1/4000",
    "latency_ticks": [0, 1, 2],
    "traces": traces,
    "de_jitter_failures": 0,
    "latest_only_failures": naive_failures,
    "max_pending_payloads": max_queue,
    "first_latest_failure": first_failure,
    "scope": "All5-message Boolean qualification patterns and three allowed delay choices, all tie delivery orders. Finite Python evidence; no loss/clockskew or physicalproof. Receive duepacket before its deadline-release phase.",
}
(HERE / "pm_protocol.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "first_latest_failure"}, indent=2))
