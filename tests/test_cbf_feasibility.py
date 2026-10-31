"""Behavioral checks for the Python and emitted-C barrier feasibility contract."""

from __future__ import annotations

import ctypes
import math
import random
import shutil
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from ctrl.robotics.codegen import emit_c99_and_iec61131
from ctrl.robotics.contact_cbf import lorentz_cbf_safety_filter


@pytest.mark.parametrize("number", [float, Fraction])
@pytest.mark.parametrize("backup_x", ["0.5", "-1"])
def test_infeasible_segment_is_reported(number, backup_x: str) -> None:
    zero, one = number(0), number(1)
    with pytest.raises(ValueError, match="no control on the nominal-to-backup segment"):
        lorentz_cbf_safety_filter(
            (one, zero, zero), one, (zero, zero, one), (number(backup_x), zero, one)
        )


@pytest.mark.parametrize("number", [float, Fraction])
def test_feasible_nominal_does_not_require_feasible_backup(number) -> None:
    zero, one = number(0), number(1)
    nominal = (one, zero, one)
    lam, result = lorentz_cbf_safety_filter((one, zero, zero), one, nominal, (zero, zero, one))
    assert lam == zero
    assert result == nominal


@pytest.mark.parametrize("number", [float, Fraction])
@pytest.mark.parametrize("barrier", ["0.5", "1"])
def test_feasible_segment_meets_barrier(number, barrier: str) -> None:
    zero, one, threshold = number(0), number(1), number(barrier)
    lam, result = lorentz_cbf_safety_filter(
        (one, zero, zero), threshold, (zero, zero, one), (one, zero, one)
    )
    assert lam == threshold
    assert result == (threshold, zero, one)


@pytest.mark.parametrize("bad", [float("nan"), float("inf"), float("-inf")])
def test_nonfinite_inputs_are_rejected(bad: float) -> None:
    with pytest.raises(ValueError, match="finite"):
        lorentz_cbf_safety_filter((1.0, 0.0, 0.0), bad, (0.0, 0.0, 1.0), (1.0, 0.0, 1.0))
    with pytest.raises(ValueError, match="finite"):
        lorentz_cbf_safety_filter((bad, 0.0, 0.0), 0.5, (0.0, 0.0, 1.0), (1.0, 0.0, 1.0))


def test_float_overflow_and_rounding_do_not_return_an_infeasible_interpolation() -> None:
    a = (1.0, 0.0, 0.0)
    # Finite dot products whose difference overflows: use the already checked backup.
    assert lorentz_cbf_safety_filter(a, 0.0, (-1e308, 0.0, 0.0), (1e308, 0.0, 0.0)) == (
        1.0,
        (1e308, 0.0, 0.0),
    )
    # This interpolation rounds one ulp below the requested threshold.
    nominal = (-946.9280606322727, 0.0, 0.0)
    backup = (-748.0896087832749, 0.0, 0.0)
    threshold = -817.706045143436
    lam, result = lorentz_cbf_safety_filter(a, threshold, nominal, backup)
    assert 0.0 < lam < 1.0
    assert result[0] >= threshold
    with pytest.raises(ValueError, match="dot products must be finite"):
        lorentz_cbf_safety_filter((1e308, 0.0, 0.0), 1.0, (2.0, 0.0, 0.0), (0.0, 0.0, 0.0))


@pytest.fixture(scope="module")
def c_filter(tmp_path_factory):
    compiler = shutil.which("cc")
    if compiler is None:
        pytest.skip("a C compiler is needed for the emitted-C behavior check")
    output = tmp_path_factory.mktemp("cbf_c")
    paths = emit_c99_and_iec61131(output)
    library = output / "libctrl_cbf.so"
    subprocess.run(
        [
            compiler,
            "-std=c99",
            "-O2",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-shared",
            "-fPIC",
            str(paths["c_source"]),
            "-o",
            str(library),
            "-lm",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    lib = ctypes.CDLL(str(library))
    vec = ctypes.c_double * 3
    function = lib.ctrl_lorentz_cbf_filter
    function.argtypes = [vec, ctypes.c_double, vec, vec, vec]
    function.restype = ctypes.c_double
    return function, vec


@pytest.mark.parametrize(
    ("threshold", "nominal", "backup"),
    [
        (0.5, (0.0, 0.0, 1.0), (1.0, 0.0, 1.0)),
        (1.0, (1.0, 0.0, 1.0), (0.0, 0.0, 1.0)),
        (0.0, (-1e308, 0.0, 0.0), (1e308, 0.0, 0.0)),
        (-817.706045143436, (-946.9280606322727, 0.0, 0.0), (-748.0896087832749, 0.0, 0.0)),
    ],
)
def test_emitted_c_matches_python_for_feasible_cases(c_filter, threshold, nominal, backup) -> None:
    function, vec = c_filter
    a = (1.0, 0.0, 0.0)
    expected_lam, expected = lorentz_cbf_safety_filter(a, threshold, nominal, backup)
    out = vec()
    lam = function(vec(*a), threshold, vec(*nominal), vec(*backup), out)
    assert lam == pytest.approx(expected_lam)
    assert list(out) == pytest.approx(expected)
    assert out[0] >= threshold


@pytest.mark.parametrize("threshold", [1.0, float("nan"), float("inf")])
def test_emitted_c_reports_infeasible_or_nonfinite(c_filter, threshold: float) -> None:
    function, vec = c_filter
    out = vec(42.0, 42.0, 42.0)
    lam = function(vec(1.0, 0.0, 0.0), threshold, vec(0.0, 0.0, 1.0), vec(0.5, 0.0, 1.0), out)
    assert math.isnan(lam)
    assert all(math.isnan(value) for value in out)


@pytest.mark.parametrize(
    ("a", "nominal", "backup"),
    [
        ((float("nan"), 0.0, 0.0), (0.0, 0.0, 1.0), (1.0, 0.0, 1.0)),
        ((1.0, 0.0, 0.0), (0.0, 0.0, 1.0), (float("inf"), 0.0, 1.0)),
        ((1e308, 0.0, 0.0), (2.0, 0.0, 0.0), (0.0, 0.0, 0.0)),
    ],
)
def test_emitted_c_rejects_invalid_vectors_and_dot_products(c_filter, a, nominal, backup) -> None:
    function, vec = c_filter
    out = vec(42.0, 42.0, 42.0)
    lam = function(vec(*a), 1.0, vec(*nominal), vec(*backup), out)
    assert math.isnan(lam)
    assert all(math.isnan(value) for value in out)
    with pytest.raises(ValueError, match="finite"):
        lorentz_cbf_safety_filter(a, 1.0, nominal, backup)


def test_feasible_multidimensional_segments_meet_the_barrier_in_python_and_c(c_filter) -> None:
    function, vec = c_filter
    rng = random.Random(72026)
    for _ in range(128):
        a = tuple(rng.uniform(-3, 3) for _ in range(3))
        nominal = tuple(rng.uniform(-3, 3) for _ in range(3))
        backup = tuple(rng.uniform(-3, 3) for _ in range(3))
        a_nom = sum(x * y for x, y in zip(a, nominal, strict=True))
        a_backup = sum(x * y for x, y in zip(a, backup, strict=True))
        if a_nom > a_backup:
            nominal, backup = backup, nominal
            a_nom, a_backup = a_backup, a_nom
        threshold = a_nom + rng.random() * (a_backup - a_nom)
        lam, result = lorentz_cbf_safety_filter(a, threshold, nominal, backup)
        out = vec()
        c_lam = function(vec(*a), threshold, vec(*nominal), vec(*backup), out)
        assert 0.0 <= lam <= 1.0
        for candidate in (result, out):
            terms = [x * y for x, y in zip(a, candidate, strict=True)]
            # dot3 uses left-to-right floating arithmetic; fsum can differ by
            # rounding, so also bound that discrepancy without claiming a proof.
            assert terms[0] + terms[1] + terms[2] >= threshold
            tolerance = 8 * math.ulp(max(1.0, abs(threshold), *(abs(term) for term in terms)))
            assert math.fsum(terms) >= threshold - tolerance
        assert c_lam == pytest.approx(lam)
        assert list(out) == pytest.approx(result)


def test_emitted_plc_interface_exposes_feasibility_status(tmp_path: Path) -> None:
    st = emit_c99_and_iec61131(tmp_path)["st_source"].read_text()
    assert "BARRIER_FEASIBLE : BOOL;" in st
