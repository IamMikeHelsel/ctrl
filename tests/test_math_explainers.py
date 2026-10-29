"""Independent finite oracles and negative cases for the explainer experiments."""

import importlib.util
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

import pytest

MODULE = Path(__file__).resolve().parents[1] / "experiments/math_explainers/run.py"
spec = importlib.util.spec_from_file_location("math_experiments", MODULE)
lab = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lab)


def test_unknown_is_not_a_proof():
    assert lab.zero_check(lab.s.Symbol("x"))["status"] == "unknown"
    with pytest.raises(AssertionError):
        lab.require_zero(lab.s.Symbol("x"))
    with pytest.raises(AssertionError):
        lab.require_zero(1)


def test_stein_with_independent_fraction_matrix_product():
    result = lab.lyapunov()
    A, P = [[[F(t) for t in row] for row in result[key]] for key in ("A", "P")]
    for i, j in product(range(2), repeat=2):
        apa = sum(A[k][i] * P[k][h] * A[h][j] for k, h in product(range(2), repeat=2))
        assert P[i][j] - apa == int(i == j)
    assert P[0][0] > 0 and P[0][0] * P[1][1] - P[0][1] ** 2 > 0
    assert result["negative_control"]["certificate"] is False


def test_braking_by_exact_subinterval_integration():
    x, v = F("1/50"), F("11/10")
    for dt in [F("1/50")] * 10:
        after = v + dt
        x += (v + after) * dt / 2
        v = after
    stop_time = v / 2
    for _ in range(13):
        dt = stop_time / 13
        after = v - 2 * dt
        x += (v + after) * dt / 2
        v = after
    assert v == 0 and x == F("273/400")
    assert x == lab.stopping_distance(F("11/10"), F("1/5"), F(1), F(2), F("1/50"))
    with pytest.raises(ValueError):
        lab.stopping_distance(F(1), F(1), F(1), F(0), F(0))


def test_schedule_bfs_against_exhaustive_slot_assignments():
    possible = list(combinations(range(4), 2))
    for mask in range(64):
        edges = [edge for i, edge in enumerate(possible) if mask & (1 << i)]
        optimum = None
        for horizon in range(1, 5):
            for slots in product(range(horizon), repeat=4):
                # Separate algorithm and predicate, without the production checker.
                if max(sum(t == slot for t in slots) for slot in range(horizon)) <= 3 and all(
                    slots[u] < slots[v] for u, v in edges
                ):
                    optimum = horizon
                    break
            if optimum is not None:
                break
        assert max(lab.optimal_schedule(4, edges)) + 1 == optimum


def test_schedule_checker_rejects_bad_certificates():
    for slots in ([0, 0, 0, 0], [0, 1, 2], [0, -1, 1, 2], [False, 1, 2, 3]):
        assert not lab.valid_schedule(4, [], slots)
    assert not lab.valid_schedule(2, [(0, 1)], [0, 0])
    with pytest.raises(ValueError, match="cyclic"):
        lab.optimal_schedule(2, [(0, 1), (1, 0)])


def test_finite_witnesses_and_negative_controls():
    witness = lab.saturation()["witness"]
    assert witness == {"bound": 1, "a": -1, "b": -1, "c": 1, "left": 0, "right": -1}
    reachable = {sum(path) for path in product((-3, 3), repeat=3)}
    assert reachable == set(lab.sumsets()["witness"]["reachable_three"])
    assert reachable == {-9, -3, 3, 9}
    assert not lab.tropical_feasible((-1, -1, 0))
    assert lab.tropical_feasible((0, -1, 0))
    assert F(lab.kalman()["negative_control"]["variance_correlated_gain"]) < F(
        lab.kalman()["negative_control"]["variance_independent_gain"]
    )


def test_report_reproducible_and_sources_resolved():
    report = lab.build_report()
    assert report == lab.build_report()
    assert len(report["experiments"]) == 8
    sources = {source["id"] for source in report["sources"]}
    assert all(set(row["source_ids"]) <= sources for row in report["experiments"])
    assert all(
        row["status"] == "completed" and row["next_test"] and row["kill_criterion"]
        for row in report["experiments"]
    )
