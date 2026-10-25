"""Adversarial contract boundaries and independent piecewise integration."""

import importlib.util
import sys
from fractions import Fraction as F
from itertools import product
from pathlib import Path

import pytest

SPEC = importlib.util.spec_from_file_location(
    "latency_braking",
    Path(__file__).resolve().parents[1] / "experiments/research/latency_braking.py",
)
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)
Contract, trajectory = MODULE.Contract, MODULE.trajectory


def test_instantaneous_rule_has_an_exact_counterexample():
    c = Contract(F(1), F(1, 10), F(1, 50), F(1, 5), F(1), F(2))
    assert c.nominal_clearance == F(1, 4)
    assert c.required_clearance == F(273, 400)
    assert c.nominal_clearance < F(1, 2) < c.required_clearance
    assert not c.admits(F(1, 2))


def test_grid_encloses_independent_lower_acceleration_and_stronger_brake_traces():
    c = Contract(F(1), F(1, 5), F(1, 50), F(1, 5), F(2), F(2))
    dt = c.delay / 4
    # Vary all four held-acceleration intervals. Integrate each segment with exact
    # trapezoidal velocity, then a stronger or equal brake until zero speed.
    for x0, v0, accels, brake in product(
        [-c.position_error, c.position_error],
        [c.speed - c.speed_error, c.upper_speed],
        list(product([F(0), c.acceleration], repeat=4)),
        [c.brake, c.brake + 1],
    ):
        x, v = x0, v0
        for a in accels:
            next_v = v + a * dt
            x += (v + next_v) * dt / 2
            v = next_v
            assert x <= c.required_clearance
        while v > 0:
            step = min(dt, v / brake)
            next_v = v - brake * step
            x += (v + next_v) * step / 2
            v = next_v
            assert x <= c.required_clearance


def test_zero_delay_reduces_to_ordinary_stopping_and_rest_is_held():
    c = Contract(F(2), F(0), F(0), F(0), F(0), F(2))
    assert c.required_clearance == c.nominal_clearance == F(1)
    assert trajectory(c, F(10)) == (F(1), F(0))
    assert c.admits(F(1))  # Boundary contact is permitted, explicitly.
    assert not c.admits(F(999, 1000))


def test_understating_delay_is_an_explicit_out_of_contract_failure():
    declared = Contract(F(1), F(0), F(0), F(0), F(0), F(2))
    actual = Contract(F(1), F(0), F(0), F(1, 2), F(0), F(2))
    assert declared.admits(F(1, 2))
    assert trajectory(actual, F(2))[0] > F(1, 2)


@pytest.mark.parametrize("bad", [float("nan"), float("inf"), True, 1.0, "1"])
def test_inexact_contracts_rejected(bad):
    with pytest.raises(TypeError):
        Contract(bad, F(0), F(0), F(0), F(0), F(1))


def test_nonphysical_parameters_rejected():
    with pytest.raises(ValueError):
        Contract(F(1), F(0), F(0), F(0), F(0), F(0))
    with pytest.raises(ValueError):
        Contract(F(1), F(0), F(0), F(-1), F(0), F(1))
