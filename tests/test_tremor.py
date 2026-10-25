"""Independent geometric checks for the conditional clock-feasibility probe."""

import runpy
from pathlib import Path

M = runpy.run_path(str(Path(__file__).resolve().parents[1] / "experiments/tremor.py"))


def test_clock_clip_keeps_true_clock_and_enforces_both_delay_bounds():
    polygon = [(0.9, -0.1), (1.1, -0.1), (1.1, 0.1), (0.9, 0.1)]
    # True host time at device time2 is2.01; arrival2.02, delay10ms.
    clipped = M["clock_update"](polygon, 2.0, 2.02, 0.02)
    assert clipped
    for rate, offset in clipped:
        assert 2.0 - 1e-12 <= 2 * rate + offset <= 2.02 + 1e-12
    # The exact admissible slice has four vertices and retains its corner extrema.
    assert abs(min(2 * a + b for a, b in clipped) - 2.0) < 1e-12
    assert abs(max(2 * a + b for a, b in clipped) - 2.02) < 1e-12


def test_inconsistent_clock_constraints_return_empty():
    polygon = [(1.0, 0.0), (1.0, 0.01), (1.01, 0.01), (1.01, 0.0)]
    assert M["clock_update"](polygon, 1.0, 3.0, 0.02) == []


def test_receipt_only_clock_model_cannot_detect_hidden_delay_world():
    polygon = [(0.9998, -0.05), (1.0002, -0.05), (1.0002, 0.05), (0.9998, 0.05)]
    # Same device stamp/receipt in two worlds: acquisition1 +delay.01,
    # or acquisition.97 +delay.04. The latter violates the declared delay envelope.
    polygon = M["clock_update"](polygon, 1.0, 1.01, 0.02)
    assert polygon
    assert min(a + b for a, b in polygon) > 0.97
    # Nonempty feasibility must never be advertised as detection of all hidden failures.


def test_no_convergence_run_cannot_report_success():
    assert M["convergence_status"]([]) is None
    assert M["convergence_status"]([{"passes_one_percent": True}]) is True
    assert (
        M["convergence_status"]([{"passes_one_percent": True}, {"passes_one_percent": False}])
        is False
    )
