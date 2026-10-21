"""Adversarial enclosure and stale-data state-machine checks for the reference sink."""

import importlib.util
import itertools
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

SPEC = importlib.util.spec_from_file_location(
    "timing_contract", Path(__file__).resolve().parents[1] / "experiments/timing_contract.py"
)
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)


def observation(**changes):
    args = dict(
        epoch=1,
        sequence=1,
        capture_lo=F(1),
        capture_hi=F(101, 100),
        position=F(1, 4),
        velocity=F(-2),
        position_error=F(1, 1000),
        velocity_error=F(1, 20),
    )
    return M.Observation(**(args | changes))


def test_every_uncertainty_corner_and_intermediate_time_is_enclosed_exactly():
    sink = M.TimingSink(1, F(1, 10), F(3))
    obs = observation()
    sink.ingest(obs)
    for now in [F(101, 100), F(103, 100), F(11, 10)]:
        pred = sink.at(now)
        assert pred.status == "ready"
        for capture, position_sign, velocity_sign, accel_sign in itertools.product(
            [obs.capture_lo, (obs.capture_lo + obs.capture_hi) / 2, obs.capture_hi],
            [-1, 1],
            [-1, 1],
            [-1, 1],
        ):
            h = now - capture
            true_position = (
                obs.position
                + position_sign * obs.position_error
                + (obs.velocity + velocity_sign * obs.velocity_error) * h
                + accel_sign * sink.acceleration_bound * h**2 / 2
            )
            assert abs(true_position - pred.center) <= pred.radius


def test_expiry_reset_and_reordering_never_return_a_command():
    sink = M.TimingSink(1, F(1, 10), F(3))
    assert sink.at(F(2)).status == "no_state"
    assert sink.ingest(observation()) == "accepted"
    assert sink.ingest(observation(position=F(99))) == "reordered_or_duplicate"
    assert sink.latest.position == F(1, 4)
    assert sink.at(F(1)).status == "acquisition_not_definitely_past"
    assert sink.at(F(2)).status == "expired"
    assert sink.at(F(2)).center is None
    assert sink.ingest(observation(epoch=2, sequence=2)) == "wrong_epoch"
    sink.reset_clock(2)
    assert sink.at(F(2)).status == "no_state"
    assert sink.ingest(observation()) == "wrong_epoch"


def test_bad_numeric_contracts_rejected():
    with pytest.raises(TypeError):
        observation(position=float("nan"))
    with pytest.raises(ValueError):
        observation(capture_lo=F(2))
    with pytest.raises(ValueError):
        observation(position_error=F(-1))


@pytest.mark.parametrize("bad", [float("nan"), 1.0, True, "2"])
def test_malformed_counters_cannot_disable_replay_rejection(bad):
    with pytest.raises(TypeError):
        observation(sequence=bad)
    with pytest.raises(TypeError):
        observation(epoch=bad)


def test_old_clock_epoch_cannot_be_reused_and_time_reversal_is_rejected():
    sink = M.TimingSink(1, F(1, 10), F(3))
    sink.ingest(observation())
    reversed_sample = observation(sequence=2, capture_lo=F(0), capture_hi=F(1, 2))
    assert sink.ingest(reversed_sample) == "time_reversal"
    assert sink.latest.sequence == 1
    sink.reset_clock(2)
    with pytest.raises(ValueError):
        sink.reset_clock(1)
    assert sink.ingest(observation()) == "wrong_epoch"


def test_overlapping_intervals_cannot_erase_earlier_ordering_constraints():
    sink = M.TimingSink(1, F(30), F(4))
    for sequence, lo, hi in [(1, 10, 20), (2, 0, 11)]:
        assert (
            sink.ingest(observation(sequence=sequence, capture_lo=F(lo), capture_hi=F(hi)))
            == "accepted"
        )
    # Adjacent overlap is insufficient: this interval precedes the first sample.
    assert sink.ingest(observation(sequence=3, capture_lo=F(1), capture_hi=F(2))) == "time_reversal"
    assert sink.latest.sequence == 2
    # A rejected interval must not poison the watermark or consume its sequence.
    assert sink.ingest(observation(sequence=3, capture_lo=F(10), capture_hi=F(10))) == "accepted"
    sink.reset_clock(2)
    assert (
        sink.ingest(observation(epoch=2, sequence=0, capture_lo=F(0), capture_hi=F(0)))
        == "accepted"
    )
