"""Exact-rational reference sink for timestamped state, not a hard-real-time controller.

AI-assisted. This exposes feasibility and uncertainty; it does not send actuator commands.
Fractions deliberately avoid claiming floating-point enclosure from real-number algebra.
"""

from dataclasses import dataclass
from fractions import Fraction as F


@dataclass(frozen=True)
class Observation:
    epoch: int
    sequence: int
    capture_lo: F
    capture_hi: F
    position: F
    velocity: F
    position_error: F
    velocity_error: F

    def __post_init__(self):
        if type(self.epoch) is not int or type(self.sequence) is not int:
            raise TypeError("Epoch and sequence must be integers, not booleans or floats")
        if self.epoch < 0:
            raise ValueError("Negative epoch")
        fields = (
            self.capture_lo,
            self.capture_hi,
            self.position,
            self.velocity,
            self.position_error,
            self.velocity_error,
        )
        if any(not isinstance(x, F) for x in fields):
            raise TypeError("Use exact Fraction values; floats are not interval certificates")
        if self.capture_lo > self.capture_hi:
            raise ValueError("Reversed acquisition interval")
        if min(self.position_error, self.velocity_error) < 0:
            raise ValueError("Negative uncertainty")
        if self.sequence < 0:
            raise ValueError("Negative sequence")


@dataclass(frozen=True)
class Prediction:
    status: str
    center: F | None = None
    radius: F | None = None
    maximum_age: F | None = None


class TimingSink:
    """One clock epoch, monotonically increasing sequence; explicit expiry.

    Sequences are assumed to follow acquisition order. Accepted intervals admit
    some nondecreasing capture-time assignment across the whole current epoch;
    this does not reveal the true capture times inside overlapping intervals.
    The caller supplies valid measurement-error, clock, and acceleration bounds.
    No receipt-only algorithm can validate every hidden violation of those bounds.
    """

    def __init__(self, epoch: int, maximum_age: F, acceleration_bound: F):
        if type(epoch) is not int or epoch < 0:
            raise ValueError("Epoch must be a nonnegative integer")
        if not isinstance(maximum_age, F) or not isinstance(acceleration_bound, F):
            raise TypeError("Bounds must be exact Fractions")
        if maximum_age <= 0 or acceleration_bound < 0:
            raise ValueError("Invalid age or acceleration bound")
        self.epoch = epoch
        self.maximum_age = maximum_age
        self.acceleration_bound = acceleration_bound
        self.latest: Observation | None = None
        self._capture_floor: F | None = None

    def reset_clock(self, epoch: int):
        """A signaled reset invalidates old state; it cannot silently reuse it."""
        if type(epoch) is not int or epoch <= self.epoch:
            raise ValueError("A reset needs a strictly increasing integer epoch")
        self.epoch = epoch
        self.latest = None
        self._capture_floor = None

    def ingest(self, sample: Observation) -> str:
        if sample.epoch != self.epoch:
            return "wrong_epoch"
        if self.latest is not None:
            if sample.sequence <= self.latest.sequence:
                return "reordered_or_duplicate"
        # The greatest lower endpoint is the earliest feasible capture time
        # after the entire accepted history, not merely the previous interval.
        if self._capture_floor is not None and sample.capture_hi < self._capture_floor:
            return "time_reversal"
        self.latest = sample
        self._capture_floor = (
            sample.capture_lo
            if self._capture_floor is None
            else max(self._capture_floor, sample.capture_lo)
        )
        return "accepted"

    def at(self, execution_time: F) -> Prediction:
        if not isinstance(execution_time, F):
            raise TypeError("Execution time must be an exact Fraction")
        obs = self.latest
        if obs is None:
            return Prediction("no_state")
        if execution_time < obs.capture_hi:
            return Prediction("acquisition_not_definitely_past")
        age = execution_time - obs.capture_lo
        if age > self.maximum_age:
            return Prediction("expired", maximum_age=age)
        midpoint = (obs.capture_lo + obs.capture_hi) / 2
        halfwidth = (obs.capture_hi - obs.capture_lo) / 2
        center = obs.position + obs.velocity * (execution_time - midpoint)
        radius = (
            obs.position_error
            + obs.velocity_error * age
            + abs(obs.velocity) * halfwidth
            + self.acceleration_bound * age**2 / 2
        )
        return Prediction("ready", center, radius, age)
