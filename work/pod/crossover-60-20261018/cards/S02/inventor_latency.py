"""Exact source-prefix detector fixture, bounded ties, and causal release policies."""

import json
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent
STEP = F(1, 2000)


def state(t):
    return (F(1, 1000) + F(39, 100) * t - F(3, 5) * t * t, F(39, 100) - F(6, 5) * t, F(-6, 5))


def guard(m):
    return m[0] <= F(143, 1000) and abs(m[1]) <= F(561, 50000) and F(-127, 100) <= m[2] <= F(-1, 5)


def reading(index):
    actual = state(index * STEP)
    return (actual[0], actual[1] + (F(1, 100) if index == 633 else 0), actual[2])


def latest_then_guard(order):
    newest = None
    first = None
    for index in order:
        if newest is None or index > newest:
            newest = index
            if first is None and guard(reading(index)):
                first = index
    return first


def prefix_certificate(records, k):
    # Records are actual packet payloads. Missing indices cannot be silently
    # certified by the largest timestamp; duplicate identities must be unique.
    indices = [i for i, _ in records]
    if len(indices) != len(set(indices)) or set(indices) != set(range(k + 1)):
        return False
    payloads = dict(records)
    return all(not guard(payloads[i]) for i in range(k)) and guard(payloads[k])


def bound_prefix_certificate(records, k, trusted_stream):
    """The trusted actual stream is external to the proposed certificate."""
    return prefix_certificate(records, k) and all(
        index in trusted_stream and payload == trusted_stream[index] for index, payload in records
    )


def main():
    first = next(k for k in range(1059) if guard(reading(k)))
    assert first == 632 and not guard(reading(633))
    stamp_old, stamp_new = F(632) * STEP, F(633) * STEP
    arrival = stamp_old + STEP
    assert arrival == stamp_new
    old, new = reading(632), reading(633)
    actual_new = state(stamp_new)
    assert new[1] - actual_new[1] == F(1, 100)
    assert old == state(stamp_old)
    assert all(
        abs(new[i] - actual_new[i]) <= (F(1, 1000), F(1, 100), F(1, 20))[i] for i in range(3)
    )
    order_results = {str(order): latest_then_guard(order) for order in permutations((632, 633))}
    assert order_results[str((633, 632))] is None
    assert order_results[str((632, 633))] == 632
    # Fixed de-jitter release keeps even an early next sample queued until its
    # own stamp+h, so arbitrary arrival ordering cannot replace the first payload.
    release_632, release_633 = stamp_old + STEP, stamp_new + STEP
    assert release_632 < release_633
    endpoint_checks = []
    for delays in product((F(0), STEP / 2, STEP), repeat=4):
        indices = list(range(630, 634))
        arrivals = [i * STEP + d for i, d in zip(indices, delays, strict=True)]
        assert all(a <= b for a, b in zip(arrivals[:-1], arrivals[1:], strict=True))
        assert max(arrivals.count(a) for a in arrivals) <= 2
        assert all(a <= (i + 1) * STEP for i, a in zip(indices, arrivals, strict=True))
        endpoint_checks.append(delays)
    full = [(k, reading(k)) for k in range(633)]
    assert prefix_certificate(full, 632)
    assert not prefix_certificate(full[:-2] + full[-1:], 632)
    assert not prefix_certificate(full + [full[-1]], 632)
    assert not prefix_certificate([(633, new)], 632)
    trusted_stream = dict(full)
    assert bound_prefix_certificate(full, 632, trusted_stream)
    forged_selected = list(old)
    forged_selected[0] += F(1, 10000)
    changed = full[:-1] + [(632, tuple(forged_selected))]
    # The logical First predicate remains true for a changed qualifying payload;
    # it cannot by itself bind a certificate to the actual source measurement.
    assert prefix_certificate(changed, 632)
    assert not bound_prefix_certificate(changed, 632, trusted_stream)
    # Old measurement propagated under the particular witness's constant target
    # -1.2 and arbitrary positive rate: the initial acceleration interval is
    # invariant since the target lies within it. This is a separate interval
    # diagnostic, not a replacement for the original C5 admission theorem.
    initial_intervals = [
        (old[i] - e, old[i] + e) for i, e in enumerate((F(1, 1000), F(1, 100), F(1, 20)))
    ]
    a_lo, a_hi = initial_intervals[2]
    v_lo, v_hi = initial_intervals[1]
    x_lo, x_hi = initial_intervals[0]
    propagated = [
        (x_lo + v_lo * STEP + a_lo * STEP**2 / 2, x_hi + v_hi * STEP + a_hi * STEP**2 / 2),
        (v_lo + a_lo * STEP, v_hi + a_hi * STEP),
        (a_lo, a_hi),
    ]
    fresh_intervals = [
        (new[i] - e, new[i] + e) for i, e in enumerate((F(1, 1000), F(1, 100), F(1, 20)))
    ]
    intersections = [
        (max(a, c), min(b, d)) for (a, b), (c, d) in zip(propagated, fresh_intervals, strict=True)
    ]
    assert all(lo <= actual_new[i] <= hi for i, (lo, hi) in enumerate(intersections))
    result = {
        "scope": "Exact actual C8 braking prefix with a new permitted velocity-noise choice at633; only prefix/tie behavior, not a newly constructed post-switch execution.",
        "step": str(STEP),
        "first_index": first,
        "sample632_state_and_reading": [str(x) for x in old],
        "sample633_actual_state": [str(x) for x in actual_new],
        "sample633_reading": [str(x) for x in new],
        "guard632": guard(old),
        "guard633": guard(new),
        "tied_arrival": str(arrival),
        "actual_information_ages": [str(STEP), "0"],
        "latest_only_order_results": order_results,
        "de_jitter_release_times": [str(release_632), str(release_633)],
        "finite_delay_checks": len(endpoint_checks),
        "no_strict_reorder_reason": "arrival(j)-arrival(i)>=(j-i-1)h>=0 for j>i with delays in[0,h]; equality can occur only for adjacent indices with delays h and0.",
        "broader_delay_counterexample": {
            "scope": "Different delay bound2h; not within original[0,h] contract.",
            "old_delay": str(2 * STEP),
            "new_delay": "0",
            "old_arrival": str(stamp_old + 2 * STEP),
            "new_arrival": str(stamp_new),
        },
        "prefix_certificate_controls": {
            "complete_pass": True,
            "missing_index_rejected": True,
            "duplicate_index_rejected": True,
            "latest_only_rejected": True,
            "unbound_changed_qualifying_payload_accepted": True,
            "bound_changed_qualifying_payload_rejected": True,
            "trust_boundary": "The immutable trusted stream must come from the actual acquisition/history interface, not certificate-supplied data. This finite experiment does not implement trusted acquisition.",
        },
        "interval_diagnostic": {
            "propagated_old_box": [[str(x) for x in box] for box in propagated],
            "fresh_reading_box": [[str(x) for x in box] for box in fresh_intervals],
            "intersection_box": [[str(x) for x in box] for box in intersections],
            "actual_state_contained": True,
            "meaning": "A later nonqualifying reading is consistent with the earlier qualifying reading and the actual pending plant; guard truth is not monotone and freshness does not erase valid earlier admission.",
        },
    }
    (HERE / "inventor_latency.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
