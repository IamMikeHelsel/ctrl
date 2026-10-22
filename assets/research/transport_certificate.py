"""Exact finite-transport certificate experiment; not a Lean or physical safety proof.

A feasible coupling supplies an upper bound. Potentials satisfying u_i + v_j <= c_ij
for every pair supply a lower bound. Exact Fraction arithmetic avoids floating-point
feasibility tolerances. Witness generation is deliberately separate from checking.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import random
from collections.abc import Sequence
from fractions import Fraction
from pathlib import Path
from typing import Any

RationalInput = int | str | Fraction


def _rational(value: RationalInput) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, str, Fraction)):
        raise ValueError("use integers, rational strings, or Fraction; floats are not accepted")
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError("invalid rational value") from exc


def _vector(values: Sequence[RationalInput]) -> tuple[Fraction, ...]:
    if isinstance(values, (str, bytes)):
        raise ValueError("a vector must be a sequence of rational values")
    return tuple(_rational(value) for value in values)


def _matrix(values: Sequence[Sequence[RationalInput]]) -> tuple[tuple[Fraction, ...], ...]:
    return tuple(_vector(row) for row in values)


def verify_certificate(
    costs: Sequence[Sequence[RationalInput]],
    source_mass: Sequence[RationalInput],
    target_mass: Sequence[RationalInput],
    coupling: Sequence[Sequence[RationalInput]],
    row_potential: Sequence[RationalInput],
    column_potential: Sequence[RationalInput],
) -> dict[str, Any]:
    """Check a finite balanced transport objective interval without solving the LP.

    The domain is all nonnegative couplings with the supplied marginals. There is
    no block mask in the checker: a lower bound must be feasible on every edge,
    including edges that a restricted candidate generator did not consider.
    """
    result: dict[str, Any] = {
        "valid": False,
        "errors": [],
        "arithmetic": "exact rational Python Fraction",
        "lean_checked": False,
    }
    try:
        c = _matrix(costs)
        a, b = _vector(source_mass), _vector(target_mass)
        p = _matrix(coupling)
        u, v = _vector(row_potential), _vector(column_potential)
    except (TypeError, ValueError) as exc:
        result["errors"].append(f"invalid_input: {exc}")
        return result

    n, m = len(a), len(b)
    if n == 0 or m == 0:
        result["errors"].append("empty_marginal")
    if len(c) != n or any(len(row) != m for row in c):
        result["errors"].append("cost_shape")
    if len(p) != n or any(len(row) != m for row in p):
        result["errors"].append("coupling_shape")
    if len(u) != n or len(v) != m:
        result["errors"].append("potential_shape")
    if any(mass < 0 for mass in (*a, *b)):
        result["errors"].append("negative_marginal")
    if sum(a) != sum(b) or sum(a) <= 0:
        result["errors"].append("unbalanced_or_nonpositive_mass")
    if result["errors"]:
        return result

    if any(value < 0 for row in p for value in row):
        result["errors"].append("negative_coupling")
    for i in range(n):
        if sum(p[i]) != a[i]:
            result["errors"].append(f"row_mass:{i}")
    for j in range(m):
        if sum(p[i][j] for i in range(n)) != b[j]:
            result["errors"].append(f"column_mass:{j}")
    for i in range(n):
        for j in range(m):
            if u[i] + v[j] > c[i][j]:
                result["errors"].append(f"dual_infeasible:{i},{j}")
    if result["errors"]:
        return result

    upper = sum(p[i][j] * c[i][j] for i in range(n) for j in range(m))
    lower = sum(a[i] * u[i] for i in range(n)) + sum(b[j] * v[j] for j in range(m))
    slack_sum = sum(p[i][j] * (c[i][j] - u[i] - v[j]) for i in range(n) for j in range(m))
    # These are redundant consistency checks of the finite weak-duality identity.
    if upper - lower != slack_sum or slack_sum < 0:
        result["errors"].append("internal_weak_duality_inconsistency")
        return result
    result.update(
        valid=True,
        lower_bound=str(lower),
        upper_bound=str(upper),
        additive_gap=str(upper - lower),
        weighted_dual_slack=str(slack_sum),
        globally_optimal=upper == lower,
        total_mass=str(sum(a)),
        interpretation="lower_bound <= global optimum <= upper_bound",
    )
    return result


def permutation_coupling(permutation: Sequence[int]) -> list[list[Fraction]]:
    n = len(permutation)
    if n == 0 or sorted(permutation) != list(range(n)):
        raise ValueError("expected a nonempty permutation")
    return [[Fraction(int(j == permutation[i]), n) for j in range(n)] for i in range(n)]


def assignment_dual(
    costs: Sequence[Sequence[RationalInput]], permutation: Sequence[int]
) -> tuple[list[Fraction], list[Fraction]]:
    """Generate exact potentials for an optimal assignment, or reject a negative cycle.

    Candidate edges are made tight. Remaining dual inequalities become difference
    constraints on column potentials. Bellman-Ford relaxation solves those constraints.
    The independent verifier must still check the returned witness.
    """
    c = _matrix(costs)
    n = len(c)
    if n == 0 or any(len(row) != n for row in c) or sorted(permutation) != list(range(n)):
        raise ValueError("expected a square cost matrix and matching permutation")
    v = [Fraction(0) for _ in range(n)]
    for iteration in range(n):
        changed = False
        for i in range(n):
            assigned = permutation[i]
            for j in range(n):
                bound = v[assigned] + c[i][j] - c[i][assigned]
                if v[j] > bound:
                    v[j] = bound
                    changed = True
        if not changed:
            return [c[i][permutation[i]] - v[permutation[i]] for i in range(n)], v
        if iteration == n - 1:
            raise ValueError("negative dual cycle: candidate assignment is not optimal")
    raise AssertionError("unreachable")


def exhaustive_assignment(
    costs: Sequence[Sequence[RationalInput]],
) -> tuple[Fraction, tuple[int, ...]]:
    """Independent tiny-instance oracle: enumerate bijections, with no dual algebra."""
    c = _matrix(costs)
    n = len(c)
    if not 1 <= n <= 7 or any(len(row) != n for row in c):
        raise ValueError("oracle accepts square instances of size 1..7")
    return min((sum(c[i][p[i]] for i in range(n)) / n, p) for p in itertools.permutations(range(n)))


def _json_rationals(value: Any) -> Any:
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, (list, tuple)):
        return [_json_rationals(item) for item in value]
    if isinstance(value, dict):
        return {key: _json_rationals(item) for key, item in value.items()}
    return value


def run_study() -> dict[str, Any]:
    """Run deterministic witnesses, independent tiny oracles, and corruptions."""
    sources, targets = [0, 1, 10, 11], [1, 2, 11, 12]
    costs = [[(x - y) ** 2 for y in targets] for x in sources]
    mass = [Fraction(1, 4)] * 4
    u, v = [-2 * x for x in sources], [2 * y - 1 for y in targets]
    oracle, _ = exhaustive_assignment(costs)
    cases = []
    for name, permutation in [
        ("aligned_assignment", [0, 1, 2, 3]),
        ("within_block_suboptimal", [1, 0, 3, 2]),
        ("crossed_block_assignment", [2, 3, 0, 1]),
    ]:
        coupling = permutation_coupling(permutation)
        check = verify_certificate(costs, mass, mass, coupling, u, v)
        assert check["valid"] and Fraction(check["lower_bound"]) <= oracle
        assert oracle <= Fraction(check["upper_bound"])
        cases.append(
            {
                "id": name,
                "costs": costs,
                "source_mass": mass,
                "target_mass": mass,
                "coupling": coupling,
                "row_potential": u,
                "column_potential": v,
                "certificate": check,
                "exhaustive_assignment_optimum": str(oracle),
                "actual_suboptimality": str(Fraction(check["upper_bound"]) - oracle),
            }
        )

    # Rectangular transport includes mass splitting, so this is not only assignment.
    rectangular = verify_certificate(
        [[0, 1, 2], [2, 1, 0]],
        ["1/2", "1/2"],
        ["1/4", "1/4", "1/2"],
        [["1/4", "1/4", 0], [0, 0, "1/2"]],
        [0, 0],
        [0, 1, 0],
    )
    assert rectangular["valid"] and rectangular["additive_gap"] == "0"

    # Unrestricted dual check catches a certificate valid only on chosen block edges.
    adversarial = {
        "mass_missing": verify_certificate(costs, mass, mass, [[0] * 4] * 4, u, v),
        "dual_forgery": verify_certificate(
            costs, mass, mass, permutation_coupling([2, 3, 0, 1]), [100] * 4, [0] * 4
        ),
        "float_input": verify_certificate([[0.0]], [1], [1], [[1]], [0], [0]),
        "negative_flow": verify_certificate(
            [[0, 1], [1, 0]],
            ["1/2"] * 2,
            ["1/2"] * 2,
            [["3/4", "-1/4"], ["-1/4", "3/4"]],
            [0, 0],
            [0, 0],
        ),
        "imbalanced_mass": verify_certificate([[0]], [1], [2], [[1]], [0], [0]),
        "wrong_shape": verify_certificate([[0]], [1], [1], [[1, 0]], [0], [0]),
    }
    assert all(not item["valid"] for item in adversarial.values())

    rng = random.Random(20261021)
    exact_witnesses = 0
    candidate_intervals = 0
    rejected_suboptimal_duals = 0
    for n in range(2, 6):
        for _ in range(6):
            c = [[rng.randint(-5, 20) for _ in range(n)] for _ in range(n)]
            optimum, permutation = exhaustive_assignment(c)
            du, dv = assignment_dual(c, permutation)
            masses = [Fraction(1, n)] * n
            exact = verify_certificate(c, masses, masses, permutation_coupling(permutation), du, dv)
            assert exact["valid"] and Fraction(exact["upper_bound"]) == optimum
            assert exact["additive_gap"] == "0"
            exact_witnesses += 1
            # Every permutation is tested independently against the exact oracle optimum.
            for candidate in itertools.permutations(range(n)):
                checked = verify_certificate(
                    c, masses, masses, permutation_coupling(candidate), du, dv
                )
                assert checked["valid"]
                assert Fraction(checked["lower_bound"]) <= optimum
                assert optimum <= Fraction(checked["upper_bound"])
                candidate_intervals += 1
                candidate_cost = sum(c[i][candidate[i]] for i in range(n)) / Fraction(n)
                if candidate_cost > optimum:
                    try:
                        assignment_dual(c, candidate)
                    except ValueError:
                        rejected_suboptimal_duals += 1
                    else:
                        raise AssertionError("suboptimal assignment obtained a tight dual")

    return _json_rationals(
        {
            "schema_version": 1,
            "study": "exact finite transport witness checks",
            "as_of": "2026-10-21",
            "seed": 20261021,
            "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "command": "uv run python experiments/research/transport_certificate.py --output work/research/2026-10/transport-results.json",
            "evidence": "deterministic Python exact-rational experiment; not Lean checked",
            "source_links": [
                "https://arxiv.org/abs/2609.38960",
                "https://arxiv.org/abs/2609.03222",
            ],
            "cases": cases,
            "rectangular_mass_splitting_certificate": rectangular,
            "adversarial_checks": adversarial,
            "oracle_validation": {
                "random_integer_cost_instances": exact_witnesses,
                "sizes": [2, 3, 4, 5],
                "certified_candidate_intervals": candidate_intervals,
                "rejected_suboptimal_tight_duals": rejected_suboptimal_duals,
                "all_checks_passed": True,
                "oracle_scope": "uniform square marginals; all permutations enumerated",
            },
            "limits": [
                "No physical navigation, dynamics, collisions, runtime deadline or floating-point implementation certified.",
                "No source algorithm, reported speedup or research novelty reproduced.",
                "Enumeration validates tiny uniform instances, not arbitrary transport problems.",
                "The weak-duality argument is implemented in trusted Python, not machine-checked Lean.",
            ],
        }
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run_study()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"output": str(args.output), "validation": result["oracle_validation"]}))


if __name__ == "__main__":
    main()
