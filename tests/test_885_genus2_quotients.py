"""Tests for tools/verify_885_genus2_quotients.py.

Verifies:
1. All 7 genus-2 quotients (6 quintics C_5^(r) and 1 sextic C_6) for Class 1 and Class 2 grids.
2. Exact Igusa-Clebsch invariants (I_2, I_4, I_6, I_10) over Q and non-vanishing discriminant I_10 != 0.
3. Exact GL_2(Q) birational invariance of absolute Igusa-Clebsch invariants (i_1, i_2, i_3) between
   the degree-6 curve C_6 and its birational degree-5 odd Weierstrass model.
4. Exact lifting of the 4 known columns V to non-Weierstrass rational points on all 7 genus-2
   quotients and compatibility under the birational transformation T = 1/(X + u_0), Y = W * T^3.
5. Exact F_p and F_{p^2} point counts, birational point-count equality for C_6 across all good
   primes p <= 53, and Hasse-Weil-Serre bounds for L_p(T) = 1 + a_1 T + a_2 T^2 + p a_1 T^3 + p^2 T^4.
6. Certification via irreducible mod-p Frobenius characteristic polynomials chi_p(x) and distinct
   real quadratic subfields Q(sqrt(Delta_y)) that all 7 Jacobians J(C_5^(r)) and J(C_6) are
   simple over Q and absolutely simple abelian surfaces over Q-bar.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.verify_885_geometry import GRID_CLASSES  # noqa: E402
from tools.verify_885_genus2_quotients import (  # noqa: E402
    PRIMES_UP_TO_53,
    analyze_all_seven_genus2_quotients,
    compute_frobenius_data_mod_p,
    compute_igusa_clebsch_from_projective_roots,
    count_projective_points_fp_and_fp2,
    is_good_prime_for_offsets,
    squarefree_part,
    verify_birational_weierstrass_model_for_c6,
)


def test_igusa_clebsch_gl2_projective_invariance() -> None:
    """Verify that absolute Igusa-Clebsch invariants (i1, i2, i3) are invariant under GL_2(Q)."""
    roots = [Fraction(r) for r in [-2, -1, 0, 1, 3, 5]]
    proj1 = [(r, Fraction(1)) for r in roots]
    inv1 = compute_igusa_clebsch_from_projective_roots(proj1)
    assert inv1.I10 > 0

    # Apply a Mobius transformation M = [[2, 3], [1, 7]] (det = 11 != 0):
    # [x : 1] -> [2*x + 3 : x + 7]
    proj2 = [(2 * r + 3, r + 7) for r in roots]
    inv2 = compute_igusa_clebsch_from_projective_roots(proj2)
    assert inv1.i1_abs == inv2.i1_abs
    assert inv1.i2_abs == inv2.i2_abs
    assert inv1.i3_abs == inv2.i3_abs


def test_birational_weierstrass_model_for_c6_all_classes() -> None:
    """Verify birational transformation of C_6 to degree-5 Weierstrass model across all 4 grid classes."""
    for cname, info in GRID_CLASSES.items():
        res = verify_birational_weierstrass_model_for_c6(info["U"], info["V"])
        assert res["abs_igusa_clebsch_match_exactly"] is True, f"Failed for {cname}"
        assert len(res["quintic_T_roots"]) == 5
        assert len(set(res["quintic_T_roots"])) == 5
        assert len(res["transformed_known_columns"]) == 4
        for col in res["transformed_known_columns"]:
            if not col["maps_to_infinity"]:
                assert col["verified_on_quintic_weierstrass"] is True


def test_frobenius_point_counts_and_birational_equality() -> None:
    """Verify that C_6 and its degree-5 Weierstrass model have identical #C(F_p) and #C(F_{p^2})."""
    U = GRID_CLASSES["class1_formB"]["U"]
    c6_roots = [Fraction(-u) for u in U]
    quintic_T_roots = [Fraction(-1, U[m] - U[0]) for m in range(1, 6)]
    quintic_lead = Fraction(1)
    for m in range(1, 6):
        quintic_lead *= U[m] - U[0]

    good_primes = [p for p in PRIMES_UP_TO_53 if is_good_prime_for_offsets(U, p)]
    assert good_primes == [31, 47, 53]

    for p in good_primes:
        fp_6, fp2_6 = count_projective_points_fp_and_fp2(c6_roots, p, degree=6)
        fp_5, fp2_5 = count_projective_points_fp_and_fp2(
            quintic_T_roots, p, degree=5, leading_coeff=quintic_lead
        )
        assert fp_6 == fp_5, f"F_p count mismatch at p={p}: {fp_6} != {fp_5}"
        assert fp2_6 == fp2_5, f"F_{{p^2}} count mismatch at p={p}: {fp2_6} != {fp2_5}"

        frob = compute_frobenius_data_mod_p(c6_roots, p, degree=6)
        assert frob.hasse_weil_valid is True
        assert frob.delta_y >= 0


def test_all_seven_genus2_quotients_class1_and_class2() -> None:
    """Verify that all 7 genus-2 quotients have simple and absolutely simple Jacobians."""
    for cname in ("class1_formB", "class2_formB"):
        res = analyze_all_seven_genus2_quotients(cname)
        assert res["num_genus2_quotients"] == 7
        assert res["all_hasse_weil_bounds_verified"] is True
        assert res["all_7_jacobians_simple_over_Q"] is True
        assert res["all_7_jacobians_absolutely_simple_over_Qbar"] is True

        quintics = [q for q in res["quotients"] if q["type"] == "quintic_genus2"]
        sextics = [q for q in res["quotients"] if q["type"] == "sextic_genus2"]
        assert len(quintics) == 6
        assert len(sextics) == 1

        for q in quintics:
            assert q["degree"] == 5
            assert q["genus"] == 2
            assert q["igusa_clebsch"]["I10_nonzero"] is True
            assert q["total_known_projective_rational_points"] == 14
            assert len(q["irreducible_frobenius_primes"]) >= 1
            assert len(q["distinct_real_quadratic_discriminants_squarefree"]) >= 2

        c6 = sextics[0]
        assert c6["degree"] == 6
        assert c6["genus"] == 2
        assert c6["igusa_clebsch"]["I10_nonzero"] is True
        assert c6["total_known_projective_rational_points"] == 16
        assert len(c6["irreducible_frobenius_primes"]) >= 1
        assert len(c6["distinct_real_quadratic_discriminants_squarefree"]) >= 2


def test_squarefree_part_helper() -> None:
    """Verify squarefree_part on positive, negative, and square inputs."""
    assert squarefree_part(1) == 1
    assert squarefree_part(12) == 3
    assert squarefree_part(72) == 2
    assert squarefree_part(-45) == -5
    assert squarefree_part(0) == 0
