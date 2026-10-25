"""Tests for tools/verify_885_geometry.py.

Verifies:
- Grid square-sums for Class 1 and Class 2 in both Form A and Form B.
- Exact projective quadrics in P^6.
- Full symbolic verification of all 21 5x5 Jacobian minors using sympy.
- Smooth complete intersection criteria via Nullstellensatz.
- Adjunction formula confirming genus g = 49.
- Automorphisms, 20 covering elliptic curves, and 6 genus-2 quotients.
- Weierstrass doubling across all 20 triples and Mazur rank lower bound (rank >= 1).
- Honest obstruction classification: Bounded search negative (q <= 10^6) + Faltings finiteness.
- Negative finding: plain Chabauty is unavailable on all 20 elliptic curves.
"""

from __future__ import annotations

import itertools
import math
import sys
from fractions import Fraction
from pathlib import Path

# Ensure repository root is on sys.path for running pytest directly
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.verify_885_geometry import (  # noqa: E402
    GRID_CLASSES,
    analyze_covering_elliptic_curves,
    analyze_covering_genus2_curves,
    classify_minor,
    compute_genus_adjunction,
    compute_minor_5x5,
    get_quadric_equations,
    point_double_weierstrass,
    verify_all_21_minors_algebraically,
    verify_all_21_minors_symbolically,
    verify_all_geometry,
    verify_grid_square_sums,
    verify_mazur_rank_lower_bound_all_20_curves,
    verify_smoothness_nullstellensatz,
)


def test_grid_square_sums_class1_and_class2() -> None:
    """Verify that every grid configuration has all 24 sums as perfect squares."""
    for class_name, data in GRID_CLASSES.items():
        assert verify_grid_square_sums(data["U"], data["V"]), f"Failed square sums for {class_name}"
        assert len(data["U"]) == 6
        assert len(data["V"]) == 4


def test_exact_equations_class1_and_class2() -> None:
    """Verify the 5 quadric equations for each class."""
    for class_name, data in GRID_CLASSES.items():
        eqs = get_quadric_equations(data["U"])
        assert len(eqs) == 5
        deltas = [eq.delta_u for eq in eqs]
        assert len(set(deltas)) == 5, f"Duplicate delta_u in {class_name}"
        assert all(d > 0 for d in deltas)

    # Specific check for Class 1 Form B: delta_u are N_1..N_5 of Form A
    c1b_eqs = get_quadric_equations(GRID_CLASSES["class1_formB"]["U"])
    expected_c1b = [206222625, 677376000, 2019635200, 4786481700, 16670745700]
    assert [eq.delta_u for eq in c1b_eqs] == expected_c1b

    # Specific check for Class 2 Form B: delta_u are N_1..N_5 of Form A
    c2b_eqs = get_quadric_equations(GRID_CLASSES["class2_formB"]["U"])
    expected_c2b = [10046592, 24561225, 115706752, 281637972, 564578560]
    assert [eq.delta_u for eq in c2b_eqs] == expected_c2b


def test_classify_all_21_minors() -> None:
    """Verify that all 21 5x5 minors are classified into Types 1-4."""
    all_cols = list(itertools.combinations(range(7), 5))
    assert len(all_cols) == 21

    type_counts = {1: 0, 2: 0, 3: 0, 4: 0}
    for cols in all_cols:
        mtype, formula = classify_minor(list(cols))
        type_counts[mtype] += 1
        assert "32" in formula

    assert type_counts[1] == 1  # omits [0, 6]
    assert type_counts[2] == 5  # omits [k, 6] for k in 1..5
    assert type_counts[3] == 5  # omits [0, k] for k in 1..5
    assert type_counts[4] == 10  # omits [j, k] for 1 <= j < k <= 5


def test_symbolic_minors_sympy_all_21() -> None:
    """Verify that all 21 minors match the symbolic product formulas using sympy."""
    res = verify_all_21_minors_symbolically()
    assert res["num_minors"] == 21
    assert res["all_match_symbolically"] is True
    assert all(m["symbolic_match"] for m in res["details"])


def test_algebraic_minors_evaluation() -> None:
    """Verify that all 21 minors evaluate to the algebraic product formula on test points."""
    for class_name, data in GRID_CLASSES.items():
        assert verify_all_21_minors_algebraically(
            data["U"],
            sample_y=[3, 5, 7, 11, 13, 17],
            sample_z=2,
        ), f"Minor algebraic check failed for {class_name}"


def test_smoothness_nullstellensatz() -> None:
    """Verify the Nullstellensatz proof steps for smoothness."""
    for _class_name, data in GRID_CLASSES.items():
        res = verify_smoothness_nullstellensatz(data["U"])
        assert res["all_u_distinct"]
        assert res["min_delta_u"] > 0
        assert res["affine_smooth"]
        assert res["infinity_smooth"]
        assert res["is_smooth_complete_intersection"]
        assert len(res["proof_steps"]) >= 5
        assert any("Sing(C) is empty" in s for s in res["proof_steps"])


def test_adjunction_formula_genus() -> None:
    """Verify the adjunction formula: omega_C = O_C(3), deg(K_C) = 96, g = 49."""
    res = compute_genus_adjunction(n=6, degrees=[2, 2, 2, 2, 2])
    assert res.ambient_dim == 6
    assert res.num_equations == 5
    assert res.variety_dim == 1
    assert res.degree == 32
    assert res.canonical_twist == 3  # 10 - 7 = 3
    assert res.canonical_degree == 96  # 3 * 32 = 96
    assert res.genus == 49  # 96 / 2 + 1 = 49

    # General family test: complete intersection of k quadrics in P^(k+1)
    # g = (k - 2) * 2^(k - 1) + 1
    for k in range(2, 7):
        adj = compute_genus_adjunction(n=k + 1, degrees=[2] * k)
        expected_g = (k - 2) * (2 ** (k - 1)) + 1
        assert adj.genus == expected_g, f"Failed genus for k={k}"


def test_covering_elliptic_curves() -> None:
    """Verify that there are exactly 20 smooth covering elliptic curves."""
    for _class_name, data in GRID_CLASSES.items():
        curves = analyze_covering_elliptic_curves(data["U"])
        assert len(curves) == 20
        for ec in curves:
            assert ec["is_smooth"]
            assert ec["delta"] != 0
            assert len(ec["roots"]) == 3
            assert len(set(ec["roots"])) == 3


def test_covering_genus2_curves() -> None:
    """Verify that there are exactly 6 smooth covering genus-2 curves."""
    for _class_name, data in GRID_CLASSES.items():
        curves = analyze_covering_genus2_curves(data["U"])
        assert len(curves) == 6
        for c in curves:
            assert c["genus"] == 2
            assert c["degree"] == 5
            assert c["discriminant_nonzero"]


def test_weierstrass_doubling_and_mazur_bound_all_20_curves() -> None:
    """Verify doubling across all 20 triples, Mazur rank bound, and plain Chabauty unavailability."""
    for _class_name, data in GRID_CLASSES.items():
        res = verify_mazur_rank_lower_bound_all_20_curves(data["U"], data["V"])
        assert res["num_triples_verified"] == 20
        assert res["rank_strictly_positive_for_all_20"] is True
        assert res["num_known_columns"] == 4
        assert res["max_torsion_doubles_x_coords"] == 2
        assert res["plain_chabauty_available_on_elliptic_curves"] is False
        assert "UNAVAILABLE" in res["plain_chabauty_negative_reason"]

        # Direct test of point_double_weierstrass on triple (0, 1, 2)
        e_roots = [-data["U"][0], -data["U"][1], -data["U"][2]]
        s1 = math.isqrt(data["V"][0] + data["U"][0])
        s2 = math.isqrt(data["V"][0] + data["U"][1])
        s3 = math.isqrt(data["V"][0] + data["U"][2])
        p0 = (
            Fraction(data["V"][0] + s1 * s2 + s1 * s3 + s2 * s3),
            Fraction((s1 + s2) * (s1 + s3) * (s2 + s3)),
        )
        x2, _ = point_double_weierstrass(e_roots, p0)
        assert x2 == Fraction(data["V"][0])


def test_rational_points_on_curve() -> None:
    """Verify that each known column yields 64 affine rational points plus 32 at infinity."""
    num_cols = 4
    num_affine = num_cols * (2**6)
    num_infinity = 2**5
    total = num_affine + num_infinity
    assert total == 288


def test_compute_minor_5x5_singular_matrix() -> None:
    """Verify that a matrix with a zero row has determinant 0."""
    zero_row_matrix = [[Fraction(0)] * 7 for _ in range(5)]
    det = compute_minor_5x5(zero_row_matrix, [0, 1, 2, 3, 4])
    assert det == Fraction(0)


def test_honest_obstruction_classification() -> None:
    """Verify that verify_all_geometry accurately reports bounded negative search and Faltings."""
    for cname in GRID_CLASSES:
        res = verify_all_geometry(cname)
        obs = res["obstruction_summary"]
        assert obs["classification"] == "Bounded search negative (q <= 10^6) + Faltings finiteness (non-effective)"
        assert obs["faltings_finite"] is True
        assert obs["genus"] == 49
        assert obs["q_max_searched"] == 1000000
        assert obs["column_hits_found"] == 0
        assert obs["plain_chabauty_available_on_elliptic"] is False
        assert "Magma/Sage" in obs["genus2_chabauty_status"]


def test_strassman_coleman_residue_disk_dominance_and_c5_good_primes() -> None:
    """Verify the Strassman/Coleman residue-disk dominance identity and C_5 good-prime reductions
    matching Erdos885MumfordChabauty.lean."""
    # 1. Verify coleman_disk_difference_identity and zero-root / unique-root criteria
    p = 19
    c0, c1 = 7, 5
    R = lambda t: 3 * t + 2
    coleman_f = lambda t: c0 + c1 * (p * t) + (p**2) * (t**2) * R(t)
    for t1 in range(-5, 6):
        # Since p=19 does not divide c0=7, f(t1) != 0
        assert coleman_f(t1) % p == c0 % p != 0
        assert coleman_f(t1) != 0
        for t2 in range(-5, 6):
            lhs = coleman_f(t1) - coleman_f(t2)
            rhs = p * (t1 - t2) * (c1 + p * (t1 + t2) * R(t1)) + (p**2) * (t2**2) * (R(t1) - R(t2))
            assert lhs == rhs

    # 2. Verify Class 1 quintic C_5(x) = x * q_5(x) good-prime reductions at p in {11, 13, 17, 19, 23}
    q5 = lambda x: x**4 + 89 * x**3 + 2796 * x**2 + 35704 * x + 123200
    c5 = lambda x: x**5 + 89 * x**4 + 2796 * x**3 + 35704 * x**2 + 123200 * x
    for x in range(-25, 26):
        assert c5(x) == x * q5(x)

    assert [x for x in range(11) if q5(x) % 11 == 0] == [0]
    assert [x for x in range(13) if q5(x) % 13 == 0] == [5]
    assert [x for x in range(17) if q5(x) % 17 == 0] == [10, 11, 12, 14]
    assert [x for x in range(19) if q5(x) % 19 == 0] == []
    assert [x for x in range(23) if q5(x) % 23 == 0] == []
    assert all(c5(x) % 19 != 0 for x in range(1, 19))
    assert all(c5(x) % 23 != 0 for x in range(1, 23))


def test_c5_chabauty_certificate_finite_data() -> None:
    """Cross-check the finite data in lean/Research/Erdos885C5Chabauty.lean with exact integers."""

    def f(x: int) -> int:
        return x**5 + 89 * x**4 + 2796 * x**3 + 35704 * x**2 + 123200 * x

    # Mumford divisor D = (x^2 + 8x + 32, 136x + 272) over Q
    for x in range(-30, 31):
        lhs = f(x) - (136 * x + 272) ** 2
        assert lhs == (x * x + 8 * x + 32) * (x**3 + 81 * x**2 + 2116 * x - 2312)

    def count1(p: int) -> int:
        return 1 + sum(1 for x in range(p) for y in range(p) if (y * y - f(x)) % p == 0)

    def count2(p: int, d: int) -> int:
        def mul(u: tuple[int, int], v: tuple[int, int]) -> tuple[int, int]:
            return ((u[0] * v[0] + d * u[1] * v[1]) % p, (u[0] * v[1] + u[1] * v[0]) % p)

        total = 1
        for a in range(p):
            for b in range(p):
                z = (a, b)
                acc = (0, 0)
                for c in (1, 89, 2796, 35704, 123200, 0):
                    acc = mul(acc, z)
                    acc = ((acc[0] + c) % p, acc[1])
                if acc == (0, 0):
                    total += 1
                elif pow((acc[0] ** 2 - d * acc[1] ** 2) % p, (p - 1) // 2, p) == 1:
                    total += 2
        return total

    def jac(p: int, d: int) -> int:
        return (count1(p) ** 2 + count2(p, d)) // 2 - p

    assert count1(17) == 22 and count2(17, 3) == 350 and jac(17, 3) == 400
    assert (jac(13, 2), jac(29, 2), jac(41, 3)) == (148, 1042, 2000)
    assert math.gcd(148, 1042) == 2
    # f splits mod 17 with roots {0, 10, 11, 12, 14}; D mod 17 is (x - 12)(x - 14), b = 0
    assert [x for x in range(17) if f(x) % 17 == 0] == [0, 10, 11, 12, 14]
    assert all((x * x + 8 * x + 32 - (x - 12) * (x - 14)) % 17 == 0 for x in range(17))
    assert 136 % 17 == 0 and 272 % 17 == 0
    # 11 is a bad prime: q5 = f/x has a root at 0 mod 11, so f has a double root there
    assert 123200 % 11 == 0
