"""Logical one-slot deadline priority versus immediate FIFO callback delivery."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
H = F(1, 2000)


def deadline_priority(indices, arrivals, expected_start, expected_count):
    expected = list(range(expected_start, expected_start + expected_count))
    deadlines = {i * H + H: i for i in expected}
    queue, released, max_payload_slots = {}, [], 0
    max_external_ready = 0
    logical_trace = []
    for now in sorted(set(arrivals) | set(deadlines)):
        # This ready list is external scheduling/storage, not counted as a
        # payload slot. That distinction is explicit in the returned evidence.
        ready = [i for i, t in zip(indices, arrivals, strict=True) if t == now]
        max_external_ready = max(max_external_ready, len(ready))

        def ingest(index, now=now):
            nonlocal max_payload_slots
            if index not in expected or not index * H <= now <= (index + 1) * H:
                raise ValueError("invalid acquisition binding or readiness time")
            if index in queue or index in released:
                raise ValueError("duplicate original identity")
            queue[index] = index * H
            max_payload_slots = max(max_payload_slots, len(queue))
            logical_trace.append((str(now), "ingest", index))
            if len(queue) > 1:
                raise ValueError("one payload slot exceeded")

        if now in deadlines:
            due = deadlines[now]
            if due not in queue:
                if due not in ready:
                    raise ValueError("due packet absent at release")
                ingest(due)
                ready.remove(due)
            queue.pop(due)
            released.append(due)
            logical_trace.append((str(now), "release", due))
        for index in reversed(ready):
            ingest(index)
    return released, max_payload_slots, max_external_ready, logical_trace


def immediate_fifo_one_slot(callback_order):
    queue = None
    released = []
    for index in callback_order:
        if queue is not None:
            return {
                "accepted": False,
                "reason": "future payload occupies only slot when due packet arrives",
            }
        queue = index
        if index == 632:  # Release deadline currently belongs to632.
            released.append(index)
            queue = None
    return {"accepted": True, "released": released, "queued": queue}


def main():
    indices = list(range(630, 635))
    count, max_slots, max_ready = 0, 0, 0
    for delays in product((F(0), H / 2, H), repeat=5):
        arrivals = [i * H + d for i, d in zip(indices, delays, strict=True)]
        released, slots, ready, _ = deadline_priority(indices, arrivals, 630, 5)
        assert released == indices
        count += 1
        max_slots, max_ready = max(max_slots, slots), max(max_ready, ready)
    tied = deadline_priority([632, 633], [633 * H, 633 * H], 632, 2)
    fifo_bad = immediate_fifo_one_slot([633, 632])
    fifo_good = immediate_fifo_one_slot([632, 633])
    assert not fifo_bad["accepted"] and fifo_good["accepted"]
    result = {
        "scope": "Logical simultaneous-event ordering and explicitly counted application payload slots. Not a total-memory bound or real-time implementation proof.",
        "tested_patterns": count,
        "max_application_slots": max_slots,
        "max_external_ready_packets": max_ready,
        "tied_logical_trace": tied[3],
        "immediate_FIFO_future_first": fifo_bad,
        "immediate_FIFO_due_first": fifo_good,
        "unbudgeted_service_negative_control": {
            "post_deadline_service_time": "1/100000",
            "first_dispatch_age": str(H + F(1, 100000)),
            "next_incoming_hold_age": str(2 * H + F(1, 100000)),
            "violates_original_startup": H + F(1, 100000) > H,
            "violates_original_total_age": 2 * H + F(1, 100000) > 2 * H,
            "required_ready_by_if_service_reserved": str(H - F(1, 100000)),
            "meaning": "A10microsecond cost after the nominal deadline violates the frozen timing contract. Reserve service within the original total bound or establish a new contract; logical same-time ordering is not a zero-time hardware claim.",
        },
        "sufficient_boundary_order": "Only due packet readiness/ingestion must precede its release. A future packet at the same real time may be ingested after that release.",
        "assumptions": [
            "Expected index interval is externally fixed by the actual acquisition schedule.",
            "Every ready event has completed all required validation and is actuation-ready within the existing bound; no payload-authentication implementation is modeled here.",
            "Scheduler can select the due packet from the external ready set or callbacks are already deadline-prioritized.",
            "Events at one real timestamp have a logical order; no claim is made that a physical processor executes them in zero time.",
            "Positive implementation service/actuation latency must fit within the original stamp+h deadline, not be added after it.",
        ],
        "conclusion": "One application slot is sufficient with the stated priority interface. Arbitrary immediate FIFO callbacks require two slots on the exhibited tie unless storage/deferral is provided elsewhere.",
    }
    (HERE / "inventor_tie_priority.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
