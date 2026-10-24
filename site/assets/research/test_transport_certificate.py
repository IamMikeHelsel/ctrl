"""Independent small oracles and invalid witnesses for finite transport certificates."""

import itertools
import runpy
from fractions import Fraction
from pathlib import Path

import pytest

MODULE = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "experiments/research/transport_certificate.py")
)
verify = MODULE["verify_certificate"]
assignment_dual = MODULE["assignment_dual"]
permutation_coupling = MODULE["permutation_coupling"]


def test_suboptimal_feasible_candidate_has_honest_global_gap():
    costs = [[0, 4], [4, 0]]
    result = verify(costs, ["1/2"] * 2, ["1/2"] * 2, [[0, "1/2"], ["1/2", 0]], [0, 0], [0, 0])
    assert result["valid"]
    assert (result["lower_bound"], result["upper_bound"], result["additive_gap"]) == (
        "0",
        "4",
        "4",
    )
    assert result["globally_optimal"] is False
    assert result["lean_checked"] is False


def test_restricted_dual_cannot_certify_unrestricted_problem():
    # The forged dual is feasible on the two used edges but not on the cheap unused edges.
    result = verify(
        [[0, 100], [100, 0]],
        ["1/2"] * 2,
        ["1/2"] * 2,
        [[0, "1/2"], ["1/2", 0]],
        [100, 100],
        [0, 0],
    )
    assert not result["valid"]
    assert result["errors"] == ["dual_infeasible:0,0", "dual_infeasible:1,1"]
    assert "lower_bound" not in result


def test_rectangular_split_mass_matches_independent_grid_enumeration():
    costs = [[0, 1, 2], [2, 1, 0]]
    result = verify(
        costs,
        ["1/2", "1/2"],
        ["1/4", "1/4", "1/2"],
        [["1/4", "1/4", 0], [0, 0, "1/2"]],
        [0, 0],
        [0, 1, 0],
    )
    # Enumerate quarter-unit flows, independently of potentials and checker formulas.
    feasible_costs = []
    for first in itertools.product(range(2), range(2), range(3)):
        if sum(first) == 2:
            second = [capacity - value for capacity, value in zip([1, 1, 2], first, strict=True)]
            feasible_costs.append(
                Fraction(sum(costs[0][j] * first[j] + costs[1][j] * second[j] for j in range(3)), 4)
            )
    assert result["valid"] and result["globally_optimal"]
    assert Fraction(result["lower_bound"]) == min(feasible_costs) == Fraction(1, 4)


def test_dual_generation_matches_every_small_two_by_two_assignment():
    for entries in itertools.product([-1, 0, 2], repeat=4):
        costs = [entries[:2], entries[2:]]
        values = {
            permutation: Fraction(sum(costs[i][permutation[i]] for i in range(2)), 2)
            for permutation in [(0, 1), (1, 0)]
        }
        optimum = min(values.values())
        for candidate, value in values.items():
            if value > optimum:
                with pytest.raises(ValueError, match="negative dual cycle"):
                    assignment_dual(costs, candidate)
            else:
                u, v = assignment_dual(costs, candidate)
                result = verify(
                    costs, ["1/2"] * 2, ["1/2"] * 2, permutation_coupling(candidate), u, v
                )
                assert result["valid"] and result["globally_optimal"]
                assert Fraction(result["lower_bound"]) == optimum


@pytest.mark.parametrize("bad", [0.0, True, "nan", "1/0", None])
def test_ambiguous_or_nonfinite_input_rejected(bad):
    result = verify([[bad]], [1], [1], [[1]], [0], [0])
    assert not result["valid"]
    assert result["errors"][0].startswith("invalid_input:")


@pytest.mark.parametrize(
    ("coupling", "error"),
    [
        ([["3/4", "-1/4"], ["-1/4", "3/4"]], "negative_coupling"),
        ([["1/4", 0], [0, "1/2"]], "row_mass:0"),
        ([["1/2", 0], ["1/2", 0]], "column_mass:0"),
        ([[1]], "coupling_shape"),
    ],
)
def test_corrupted_couplings_rejected(coupling, error):
    result = verify([[0, 1], [1, 0]], ["1/2"] * 2, ["1/2"] * 2, coupling, [0, 0], [0, 0])
    assert not result["valid"]
    assert error in result["errors"]


def test_total_mass_need_not_equal_one_and_zero_mass_rows_are_allowed():
    result = verify([[3], [7]], [2, 0], [2], [[2], [0]], [3, 7], [0])
    assert result["valid"] and result["globally_optimal"]
    assert result["upper_bound"] == "6" and result["total_mass"] == "2"


@pytest.mark.parametrize(
    ("source", "target", "error"),
    [
        ([1], [2], "unbalanced_or_nonpositive_mass"),
        ([0], [0], "unbalanced_or_nonpositive_mass"),
        ([-1], [-1], "negative_marginal"),
        ([], [], "empty_marginal"),
    ],
)
def test_invalid_marginals_rejected(source, target, error):
    result = verify([[0]], source, target, [[1]], [0], [0])
    assert not result["valid"]
    assert error in result["errors"]
