"""Independent certificate replay and fail-closed exploratory search checks."""

import runpy
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
CHECKER = runpy.run_path(str(ROOT / "work/273/check_seven.py"))
PROBE = runpy.run_path(str(ROOT / "work/273/smooth_probe.py"))


def test_independent_seven_certificate_and_corruption_rejection():
    result = CHECKER["check"](CHECKER["MASS_BOUNDS"], CHECKER["MIN_GAP"])
    assert result["checked_assignments"] == 720
    assert result["minimum_density_margin"] == "57/10000"
    assert CHECKER["mutation_checks"]() == 4


def test_search_limit_cannot_be_reported_as_exclusion():
    result = PROBE["probe"]([2, 3, 5, 7], [10, 6, 4, 3], [4, 6, 10, 12], 1)
    assert result["completion"] == "node_limit"
    assert not result["excluded_by_python_bound"]


@pytest.mark.parametrize(
    ("primes", "caps", "prefix"),
    [
        ([2, 3, 5, 7], [10, 6, 4, 3], [4, 6, 48]),
        ([2, 3, 5, 7], [10, 6, 4, 3], [4, 4, 6]),
        ([2, 3, 9], [10, 6, 4], [4, 6]),
        ([2, 3, 5], [10, 6], [4, 6]),
    ],
)
def test_invalid_models_rejected(primes, caps, prefix):
    with pytest.raises(ValueError):
        PROBE["probe"](primes, caps, prefix, 100)
