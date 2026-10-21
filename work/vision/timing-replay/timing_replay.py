"""Exact analytic reversal/reset replay; AI-assisted, no plant or actuator integration.

Run with uv run experiments/timing_replay.py. All checks use rational arithmetic.
The negative controls deliberately violate model assumptions and must escape enclosure.
"""

import hashlib
import itertools
import json
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

from timing_contract import Observation, TimingSink


def position(t):
    return t - t**3 / 3


def velocity(t):
    return 1 - t**2


def reversal_replay(acceleration_bound):
    """q'=1-t² changes sign at t=1; |q''|≤4 and q'''=-2 on [0,2]."""
    sink = TimingSink(0, F(60, 1000), acceleration_bound)
    events = [(F(1), 0, None)]  # Signaled reset happens before same-time arrivals.
    for index in range(101):
        capture = F(index, 50)
        if F(72, 100) <= capture <= F(88, 100):
            continue  # A blackout forces expiry, including before the reversal.
        epoch = int(capture >= 1)
        obs = Observation(
            epoch,
            index - 50 * epoch,
            capture - F(2, 1000),
            capture + F(2, 1000),
            position(capture) + (-1) ** index * F(1, 10000),
            velocity(capture) + (-1) ** (index // 2) * F(1, 100),
            F(1, 10000),
            F(1, 100),
        )
        receipt = capture + F([0, 3, 7, 25, 80][index % 5], 1000)
        if index == 50:
            receipt += F(10, 1000)  # The new epoch has no observation for its first 10 ms.
        events.extend([(receipt, 1, obs), (receipt + F(4, 1000), 2, obs)])
    events.sort(key=lambda x: (x[0], x[1]))
    cursor = 0
    counts = Counter()
    queries = []
    violations = []
    for tick in range(2001):
        now = F(tick, 1000)
        while cursor < len(events) and events[cursor][0] <= now:
            receipt, kind, obs = events[cursor]
            if kind == 0:
                sink.reset_clock(1)
                counts["reset"] += 1
                assert sink.at(now).status == "no_state"
            else:
                before = sink.latest
                status = sink.ingest(obs)
                counts["ingest_" + status] += 1
                if status != "accepted":
                    assert sink.latest is before
            cursor += 1
        prediction = sink.at(now)
        counts["query_" + prediction.status] += 1
        row = {"t": str(now), "status": prediction.status}
        if prediction.status == "ready":
            assert sink.latest.epoch == sink.epoch
            error = abs(position(now) - prediction.center)
            enclosed = error <= prediction.radius
            row.update(
                epoch=sink.epoch,
                sequence=sink.latest.sequence,
                center=str(prediction.center),
                radius=str(prediction.radius),
                truth=str(position(now)),
                enclosed=enclosed,
            )
            if not enclosed:
                violations.append(tick)
        else:
            assert prediction.center is None and prediction.radius is None
        queries.append(row)
    return {
        "acceleration_bound": str(acceleration_bound),
        "counts": dict(counts),
        "enclosure_violations": len(violations),
        "first_violation_tick": next(iter(violations), None),
        "queries": queries,
    }


def exhaustive_ordering():
    """Independent finite oracle: enumerate feasible true capture assignments."""
    intervals = [(F(lo), F(hi)) for lo in range(4) for hi in range(lo, 4)]
    checked = 0
    accepted = rejected = 0
    for chain in itertools.product(intervals, repeat=3):
        sink = TimingSink(0, F(10), F(0))
        history = []
        for sequence, (lo, hi) in enumerate(chain):
            candidate = history + [(lo, hi)]
            feasible = any(
                all(a <= t <= b for t, (a, b) in zip(times, candidate, strict=True))
                and all(a <= b for a, b in itertools.pairwise(times))
                for times in itertools.product(map(F, range(4)), repeat=len(candidate))
            )
            status = sink.ingest(Observation(0, sequence, lo, hi, F(0), F(0), F(0), F(0)))
            assert (status == "accepted") == feasible, (chain, sequence, status, feasible)
            checked += 1
            if feasible:
                accepted += 1
                history = candidate
            else:
                rejected += 1
        sink.reset_clock(1)
        assert sink.ingest(Observation(1, 0, F(0), F(0), F(0), F(0), F(0), F(0))) == ("accepted")
    return {"chains": 1000, "decisions": checked, "accepted": accepted, "rejected": rejected}


def reset_boundaries():
    old = Observation(0, 9, F(0), F(0), F(0), F(1), F(0), F(0))
    sink = TimingSink(0, F(1), F(0))
    sink.ingest(old)
    cached = sink.at(F(1, 10))
    sink.reset_clock(1)
    assert sink.at(F(1, 10)).status == "no_state"
    assert sink.ingest(old) == "wrong_epoch"
    # An immutable object already handed to another component is not revoked.
    assert cached.status == "ready" and cached.center == F(1, 10)
    return {
        "requery_after_reset": "no_state",
        "old_packet_after_reset": "wrong_epoch",
        "cached_prediction_is_not_revoked": True,
        "consumer_obligation": "Re-query at application; do not queue unversioned predictions.",
    }


def main():
    root = Path("work/vision/timing-replay")
    root.mkdir(parents=True, exist_ok=True)
    hashes = {}
    for source in [Path(__file__), Path(__file__).with_name("timing_contract.py")]:
        target = root / source.name
        target.write_bytes(source.read_bytes())
        hashes[str(target)] = hashlib.sha256(target.read_bytes()).hexdigest()
    valid = reversal_replay(F(4))
    invalid = reversal_replay(F(0))
    assert valid["enclosure_violations"] == 0
    assert invalid["enclosure_violations"] > 0
    for status in ["query_expired", "query_no_state", "query_acquisition_not_definitely_past"]:
        assert valid["counts"].get(status, 0) > 0
    assert valid["counts"].get("ingest_wrong_epoch", 0) > 0
    for name, result in [("valid-bound", valid), ("false-bound", invalid)]:
        (root / f"{name}-trace.json").write_text(json.dumps(result.pop("queries"), indent=2) + "\n")
    result = {
        "status": "complete",
        "kind": "exact synthetic analytic replay, not closed-loop physical simulation",
        "source_hashes": hashes,
        "trajectory": "q=t-t^3/3, v=1-t^2, t in [0,2]; reversal t=1; |a|<=4, jerk=-2",
        "sample_hz": 50,
        "query_hz": 1000,
        "clock_halfwidth_seconds": "1/500",
        "maximum_age_seconds": "3/50",
        "delay_milliseconds_cycle": [0, 3, 7, 25, 80],
        "blackout_capture_interval": ["18/25", "22/25"],
        "reset_time_seconds": "1",
        "first_new_epoch_packet_extra_delay_seconds": "1/100",
        "valid_bound": valid,
        "invalid_bound_negative_control": invalid,
        "ordering_oracle": exhaustive_ordering(),
        "reset_boundary": reset_boundaries(),
        "limits": [
            "Clock intervals and state-error bounds supplied using synthetic ground truth.",
            "No runtime clock calibration or automatic reset detector is tested.",
            "No actuator, plant integration, deadline, stability, or passivity result.",
            "No numerical integration: exact analytic evaluation requires no step convergence.",
            "Global interval consistency does not establish true hidden capture order.",
            "Classical bound propagation and interval feasibility; no novelty claim.",
        ],
    }
    (root / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
