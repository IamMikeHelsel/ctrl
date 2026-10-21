"""Exact prospective adapter model, not an implementation of the source executor."""

import json
from dataclasses import asdict, dataclass, replace
from fractions import Fraction as Q
from pathlib import Path


@dataclass(frozen=True)
class Snapshot:
    events: tuple = ((Q(11, 50), Q(1, 50)),)
    offset: Q = Q(0)
    width: Q = Q(1, 5)
    task: tuple = (Q(0), Q(13, 25), Q(17, 10), Q(1, 10), Q(1, 2), Q(15, 2))
    history_version: int = 7
    task_version: int = 10
    frame: str = "world-x"
    calibration: int = 1
    clock_map: int = 1
    units: str = "metre-second"
    authority_epoch: int = 1


@dataclass(frozen=True)
class Candidate:
    snapshot: Snapshot
    execution: Q = Q(31, 50)
    delta: Q = Q(-1, 50)
    # This abstracts the already-checked source certificate, not a new proof of it.
    checked_certificate: bool = True


@dataclass(frozen=True)
class Timing:
    estimate: Q = Q(57, 100)
    commit_clock_error: Q = Q(1, 1000)
    execution_clock_error: Q = Q(1, 1000)
    read_age: Q = Q(2, 1000)
    publication_tail: Q = Q(3, 1000)
    dispatch: Q = Q(1, 100)


def ordering(candidate, timing):
    terms = (
        timing.commit_clock_error,
        timing.execution_clock_error,
        timing.read_age,
        timing.publication_tail,
        timing.dispatch,
    )
    return all(t >= 0 for t in terms) and (
        timing.estimate
        + timing.commit_clock_error
        + timing.read_age
        + timing.publication_tail
        + timing.dispatch
        <= candidate.execution - timing.execution_clock_error
    )


def atomic_step(candidate, live, timing):
    """Arguments must be captured at one linearization point; this is a premise."""
    if not candidate.checked_certificate or live != candidate.snapshot:
        return live, "snapshot-or-certificate-reject"
    if not ordering(candidate, timing):
        return live, "time-reject"
    return replace(
        live,
        events=live.events + ((candidate.execution, candidate.delta),),
        history_version=live.history_version + 1,
    ), "accepted"


def main():
    base = Snapshot()
    pending = Candidate(base)
    timing = Timing()
    mutations = {
        "events_same_version": replace(base, events=base.events + ((Q(14, 25), Q(1, 1000)),)),
        "offset_same_version": replace(base, offset=Q(1, 1000)),
        "width_same_version": replace(base, width=Q(1, 4)),
        "task_same_version": replace(base, task=(Q(1, 200),) + base.task[1:]),
        "frame_same_version": replace(base, frame="camera-x"),
        "calibration_same_version": replace(base, calibration=2),
        "clock_mapping_same_version": replace(base, clock_map=2),
        "units_same_version": replace(base, units="millimetre-second"),
        "authority_restart": replace(base, authority_epoch=2),
    }
    rejected = {}
    for name, live in mutations.items():
        output, result = atomic_step(pending, live, timing)
        assert result != "accepted" and output == live
        assert live.history_version == base.history_version
        assert live.task_version == base.task_version
        rejected[name] = result
    once, status = atomic_step(pending, base, timing)
    assert status == "accepted" and once.events[:-1] == base.events
    twice, status2 = atomic_step(pending, once, timing)
    assert status2 != "accepted" and twice == once
    boundary = replace(timing, read_age=Q(35, 1000))
    assert ordering(pending, boundary)
    expired = replace(boundary, read_age=Q(36, 1000))
    assert not ordering(pending, expired)
    assert atomic_step(pending, base, expired) == (base, "time-reject")
    # Data-only CAS succeeds here, but the actual delivery inequality is false.
    assert base == pending.snapshot
    # Removing any positive timing allocation can accept an unsafe boundary.
    omitted = {}
    for field in (
        "commit_clock_error",
        "execution_clock_error",
        "read_age",
        "publication_tail",
        "dispatch",
    ):
        damaged = replace(expired, **{field: Q(0)})
        omitted[field] = ordering(pending, damaged)
        assert omitted[field]
    result = {
        "mutations_rejected": rejected,
        "first_commit": "accepted",
        "duplicate": status2,
        "latest_read_age": "7/200",
        "expired_read_age": "9/250",
        "data_only_cas_still_equal_at_expiry": True,
        "omitted_timing_terms_accept_expired": omitted,
        "accepted_state": asdict(once),
        "scope": "Finite typed transition model with abstract checked certificate and assumed atomic call. No concurrency primitive, memory model, physical scheduler, or real timestamp mapping proof.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, default=str, indent=2) + "\n")
    print(
        json.dumps({"mutations": len(rejected), "timing_mutations": len(omitted), "result": "pass"})
    )


if __name__ == "__main__":
    main()
