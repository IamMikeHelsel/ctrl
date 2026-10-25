"""Test Suite for Exact Rational Semidefinite and Algebraic Certificates (Lane MF-13).

Covers:
1. Exact rational linear algebra for 6x6 Byers-Nash pairs:
   - Trace moments m0, m1, m2.
   - Sylvester operator Phi_{K,Y} rank (12) and nullity (9).
   - Augmented system consistency and particular solution H0.
   - Zero-residual verification of bilateral equations AK + KA^T = Y and A^T Y + YA = K.
2. Common-T Involution Exact-SOS Algebraic Certifier:
   - Calibration pair diag(J, 2J, 3J) at A = (1/2) I_6.
   - Householder-conjugated non-block Common-T pair.
   - Exact pairing <Xu, L_A(Xv)> = ||Y||^2 proving s(A) >= 1 identically on the 8D locus.
3. Full 21x21 Dual SDP Rational Certificate:
   - Calibration pair dual certificate W_Q in Q^{21x21}.
   - Exact rational LDL^T factorization with all 21 pivots D_i > 0.
   - Verification of affine orthogonality constraints and certified bound >= 1.
4. Gram Tester Rational Certificate (Card M05):
   - Card M05 at t=1/2: exact 9x9 Gram LDL^T > 0, certified s(A)^2 >= 1.6558 > 1.
   - Card M05 at t=1/3: exact 9x9 Gram LDL^T > 0, certified s(A)^2 >= 5.390 > 1.
5. Integrity & Tamper Rejection:
   - Detection and rejection of non-involutive T, broken anticommutation, and incompatible pairs.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

# Ensure repository root is on sys.path
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import pytest  # noqa: E402

from tools.certify_mf13_pair import (  # noqa: E402
    analyze_byers_nash_pair,
    certify_common_t_involution,
    certify_dual_sdp_pair,
    certify_gram_tester_pair,
    find_common_t_involution,
    frobenius_inner,
    make_calibration_pair,
    make_householder_conjugated_pair,
    make_m05_pair,
    make_mixed_j_anticomm_pair,
    make_pure_j_commuting_pair,
    off_diagonal_energy_decomposition,
    phi_operator,
    rhs_operator,
    run_mf13_benchmark_suite,
    standard_skew_basis_6,
    standard_symmetric_basis_6,
    trace_moments,
)
from tools.sdp_rational_cert import RationalMatrix, verify_ldl_identity  # noqa: E402

# ==============================================================================
# 1. Exact Linear Algebra for 6x6 Byers-Nash Skew Pairs
# ==============================================================================


def test_standard_bases_properties():
    """Verify standard bases of S_6 (21 dims) and K_6 (15 dims)."""
    sym = standard_symmetric_basis_6()
    skew = standard_skew_basis_6()

    assert len(sym) == 21
    assert len(skew) == 15

    # Check symmetry and skew-symmetry
    for S in sym:
        assert (S - S.transpose()).max_abs_entry() == Fraction(0)
    for K in skew:
        assert (K + K.transpose()).max_abs_entry() == Fraction(0)

    # Check orthogonality
    for i in range(21):
        for j in range(i + 1, 21):
            assert frobenius_inner(sym[i], sym[j]) == Fraction(0)

    for i in range(15):
        for j in range(i + 1, 15):
            assert frobenius_inner(skew[i], skew[j]) == Fraction(0)


def test_calibration_pair_linear_reduction():
    """Verify trace moments, Sylvester rank/nullity, and affine family on calibration pair."""
    K, Y, A, T = make_calibration_pair()

    # Moments
    moms = trace_moments(K, Y, num_moments=3)
    assert moms == [Fraction(0), Fraction(0), Fraction(0)]

    # Analysis
    analysis = analyze_byers_nash_pair(K, Y)
    assert analysis.K_rank == 6
    assert analysis.Y_rank == 6
    assert analysis.phi_rank == 12
    assert analysis.phi_nullity == 9
    assert analysis.is_compatible is True
    assert analysis.residual_A0_K == "0"
    assert analysis.residual_A0_Y == "0"

    # Verify H0 satisfies Phi(H0) == RHS
    H0 = RationalMatrix([[Fraction(x) for x in row] for row in analysis.H0])
    Phi_H0 = phi_operator(K, Y, H0)
    RHS = rhs_operator(K, Y)
    assert (Phi_H0 - RHS).max_abs_entry() == Fraction(0)

    # Verify all 9 directions satisfy homogeneous equation Phi(Hr) == 0
    for Hr_data in analysis.kernel_H_basis:
        Hr = RationalMatrix([[Fraction(x) for x in row] for row in Hr_data])
        Phi_Hr = phi_operator(K, Y, Hr)
        assert Phi_Hr.max_abs_entry() == Fraction(0)

    # Verify A(z) bilateral equations for test points in the 9D affine space
    A0 = RationalMatrix([[Fraction(x) for x in row] for row in analysis.A0])
    dirs = [
        RationalMatrix([[Fraction(x) for x in row] for row in Ar_data])
        for Ar_data in analysis.affine_directions_A
    ]

    for test_z in [
        [Fraction(0)] * 9,
        [Fraction(1, 3)] * 9,
        [Fraction(i, 7) for i in range(1, 10)],
    ]:
        A_z = A0
        for direction, zi in zip(dirs, test_z, strict=True):
            A_z = A_z + (direction * zi)
        res_K = (A_z @ K) + (K @ A_z.transpose()) - Y
        res_Y = (A_z.transpose() @ Y) + (Y @ A_z) - K
        assert res_K.max_abs_entry() == Fraction(0)
        assert res_Y.max_abs_entry() == Fraction(0)


# ==============================================================================
# 2. Common-T Involution Exact Algebraic Certifier
# ==============================================================================


def test_calibration_common_t_involution():
    """Verify algebraic certificate on calibration pair diag(J, 2J, 3J) at A = (1/2) I_6."""
    K, Y, A, T = make_calibration_pair()

    # Automatically find involution
    T_found = find_common_t_involution(K, Y)
    assert T_found is not None
    assert (T_found @ T_found - RationalMatrix.identity(6)).max_abs_entry() == Fraction(0)

    # Certify with known T
    cert = certify_common_t_involution(K, Y, T, A, name="Calibration Test")
    assert cert.is_symmetric is True
    assert cert.is_involutive is True
    assert cert.anticommutes_K is True
    assert cert.anticommutes_Y is True
    assert cert.Xv_is_symmetric is True
    assert cert.Xu_is_symmetric is True
    assert cert.Xv_frobenius_sq == "28"
    assert cert.Xu_frobenius_sq == "28"
    assert cert.pairing_Xu_L_A_Xv == "28"
    assert cert.pairing_equals_Y_frobenius_sq is True
    assert cert.certified_s_bound == "1"
    assert cert.status == "CERTIFIED_IDENTICALLY"


def test_conjugated_common_t_family():
    """Verify algebraic certificate on a non-block-diagonal conjugated common-T pair."""
    K_conj, Y_conj, T_conj = make_householder_conjugated_pair([1, 2, 3, 4, 5, 6])

    # Check that K_conj is not block diagonal
    # (has nonzero entries in positions outside the 2x2 blocks)
    has_cross_block_entries = False
    for i in range(2):
        for j in range(2, 6):
            if K_conj.data[i][j] != Fraction(0):
                has_cross_block_entries = True
    assert has_cross_block_entries is True

    # Certify
    cert = certify_common_t_involution(K_conj, Y_conj, T_conj, name="Conjugated Common-T")
    assert cert.is_symmetric is True
    assert cert.is_involutive is True
    assert cert.anticommutes_K is True
    assert cert.anticommutes_Y is True
    assert cert.pairing_equals_Y_frobenius_sq is True
    assert cert.certified_s_bound == "1"
    assert cert.status == "CERTIFIED_IDENTICALLY"


# ==============================================================================
# 3. Card M05 Candidates at t=1/2 and t=1/3
# ==============================================================================


def test_card_m05_t_half_certification():
    """Verify Card M05 pair at t=1/2: moments, 9D affine family, and Gram LDL^T certificate."""
    K, Y, Q = make_m05_pair("1/2")

    # 1. Check moments
    moms = trace_moments(K, Y, num_moments=3)
    assert moms == [Fraction(0), Fraction(0), Fraction(0)]

    # 2. Check analysis
    analysis = analyze_byers_nash_pair(K, Y)
    assert analysis.phi_rank == 12
    assert analysis.phi_nullity == 9
    assert analysis.is_compatible is True
    assert analysis.residual_A0_K == "0"
    assert analysis.residual_A0_Y == "0"

    # 3. Certify with Gram tester using Q and I_6
    tests = [(Q, Fraction(1)), (RationalMatrix.identity(6), Fraction(1))]
    cert = certify_gram_tester_pair(K, Y, tests=tests, name="Card M05 t=1/2")

    assert cert.dim == 9
    # Verify all 9 pivots are strictly positive
    pivots = [Fraction(p) for p in cert.D]
    assert len(pivots) == 9
    assert all(p > 0 for p in pivots)

    # Verify G == L D L^T exactly
    G_mat = RationalMatrix([[Fraction(x) for x in row] for row in cert.Gram])
    L_mat = RationalMatrix([[Fraction(x) for x in row] for row in cert.L])
    is_valid_ldl, max_err = verify_ldl_identity(L_mat, pivots, G_mat)
    assert is_valid_ldl is True
    assert max_err == Fraction(0)

    # Verify lower bound strictly exceeds 1
    bound = Fraction(cert.certified_s_sq_bound)
    assert bound > Fraction(1)
    # Numerical value is approx 1.6558 > 1
    assert float(bound) > 1.6
    assert cert.excludes_s_below_one is True
    assert cert.status == "CERTIFIED_GRAM_TESTER"


def test_card_m05_t_third_certification():
    """Verify Card M05 pair at t=1/3: moments, 9D affine family, and Gram LDL^T certificate."""
    K, Y, Q = make_m05_pair("1/3")

    moms = trace_moments(K, Y, num_moments=3)
    assert moms == [Fraction(0), Fraction(0), Fraction(0)]

    analysis = analyze_byers_nash_pair(K, Y)
    assert analysis.phi_rank == 12
    assert analysis.phi_nullity == 9
    assert analysis.is_compatible is True

    tests = [(Q, Fraction(1)), (RationalMatrix.identity(6), Fraction(1))]
    cert = certify_gram_tester_pair(K, Y, tests=tests, name="Card M05 t=1/3")

    pivots = [Fraction(p) for p in cert.D]
    assert len(pivots) == 9
    assert all(p > 0 for p in pivots)

    G_mat = RationalMatrix([[Fraction(x) for x in row] for row in cert.Gram])
    L_mat = RationalMatrix([[Fraction(x) for x in row] for row in cert.L])
    is_valid_ldl, max_err = verify_ldl_identity(L_mat, pivots, G_mat)
    assert is_valid_ldl is True
    assert max_err == Fraction(0)

    bound = Fraction(cert.certified_s_sq_bound)
    assert bound > Fraction(1)
    # Numerical value is approx 5.390 > 1
    assert float(bound) > 5.0
    assert cert.excludes_s_below_one is True


# ==============================================================================
# 4. 21x21 Dual SDP Certificate
# ==============================================================================


def test_dual_sdp_21x21_calibration():
    """Verify 21x21 rational dual SDP certificate on calibration pair."""
    K, Y, _, _ = make_calibration_pair()

    cert = certify_dual_sdp_pair(K, Y, name="Calibration 21x21 Dual SDP")
    assert cert.dim == 21
    assert cert.trace_W == "1"

    pivots = [Fraction(p) for p in cert.D]
    assert len(pivots) == 21
    assert all(p > 0 for p in pivots)
    assert cert.is_strictly_positive_definite is True

    # Check LDL^T identity on W_Q
    W_Q = RationalMatrix([[Fraction(x) for x in row] for row in cert.W_Q])
    L = RationalMatrix([[Fraction(x) for x in row] for row in cert.L])
    is_valid, max_err = verify_ldl_identity(L, pivots, W_Q)
    assert is_valid is True
    assert max_err == Fraction(0)

    # Check that all affine orthogonality errors are exactly zero
    for err_str in cert.affine_orthogonality_errors:
        assert Fraction(err_str) == Fraction(0)

    # Certified bound >= 1
    bound = Fraction(cert.certified_bound)
    assert bound >= Fraction(1)
    assert cert.status == "CERTIFIED_STRICT_SDP"


# ==============================================================================
# 5. Full Benchmark Suite and Tamper Resistance
# ==============================================================================


def test_pure_j_commuting_and_mixed_j_anticomm_pairs():
    """Verify exact 15D energy split and rational certificates on pure-J and mixed (J, {I2,F,G}) pairs."""
    # 1. Pure W_pq-commuting (J) off-diagonal pair
    K_pj, Y_pj, Q_pj, T0_pj = make_pure_j_commuting_pair()
    moms_pj = trace_moments(K_pj, Y_pj, num_moments=3)
    assert moms_pj == [Fraction(0), Fraction(0), Fraction(0)]

    split_pj = off_diagonal_energy_decomposition(Y_pj)
    assert split_pj["parseval_exact"] is True
    assert split_pj["diag_frobenius_sq"] == "220/9"
    assert split_pj["off_diag_anticomm_frobenius_sq"] == "0"
    assert split_pj["off_diag_comm_j_frobenius_sq"] == "32/9"
    assert split_pj["total_frobenius_sq"] == "28"

    cert_pj_inv = certify_common_t_involution(K_pj, Y_pj, T0_pj, name="Pure J Off-Diag Common-T0")
    assert cert_pj_inv.status == "CERTIFIED_IDENTICALLY"
    assert cert_pj_inv.certified_s_bound == "1"

    cert_pj_gram = certify_gram_tester_pair(
        K_pj,
        Y_pj,
        tests=[
            (Q_pj, Fraction(1)),
            (T0_pj, Fraction(1)),
            (RationalMatrix.identity(6), Fraction(1)),
        ],
        name="Pure J Off-Diag Gram",
    )
    assert cert_pj_gram.excludes_s_below_one is True
    assert Fraction(cert_pj_gram.certified_s_sq_bound) == Fraction(10153, 729)
    pivots_pj = [Fraction(p) for p in cert_pj_gram.D]
    assert all(p > 0 for p in pivots_pj)

    # 2. Adversarial mixed (J, {I2, F, G}) off-diagonal pair with zero Common-T subspace
    K_mix, Y_mix, Q_mix = make_mixed_j_anticomm_pair("1/3", "1/3")
    moms_mix = trace_moments(K_mix, Y_mix, num_moments=3)
    assert moms_mix == [Fraction(0), Fraction(0), Fraction(0)]
    assert find_common_t_involution(K_mix, Y_mix) is None

    split_mix = off_diagonal_energy_decomposition(Y_mix)
    assert split_mix["parseval_exact"] is True
    assert Fraction(split_mix["off_diag_comm_j_frobenius_sq"]) > Fraction(
        split_mix["diag_frobenius_sq"]
    )
    assert Fraction(split_mix["off_diag_anticomm_frobenius_sq"]) > Fraction(0)

    cert_mix_gram = certify_gram_tester_pair(
        K_mix,
        Y_mix,
        tests=[
            (Q_mix, Fraction(6)),
            (T0_pj, Fraction(1)),
            (RationalMatrix.identity(6), Fraction(1)),
        ],
        name="Adversarial Mixed (J, {I2,F,G}) Gram",
    )
    assert cert_mix_gram.excludes_s_below_one is True
    assert Fraction(cert_mix_gram.certified_s_sq_bound) > Fraction(1)
    pivots_mix = [Fraction(p) for p in cert_mix_gram.D]
    assert all(p > 0 for p in pivots_mix)
    G_mix = RationalMatrix([[Fraction(x) for x in row] for row in cert_mix_gram.Gram])
    L_mix = RationalMatrix([[Fraction(x) for x in row] for row in cert_mix_gram.L])
    is_valid_mix, max_err_mix = verify_ldl_identity(L_mix, pivots_mix, G_mix)
    assert is_valid_mix is True
    assert max_err_mix == Fraction(0)


def test_run_mf13_benchmark_suite():
    """Verify that run_mf13_benchmark_suite executes cleanly and returns all certificates."""
    results = run_mf13_benchmark_suite()
    assert "calibration" in results
    assert "m05_t_half" in results
    assert "m05_t_third" in results
    assert "conjugated_common_t" in results
    assert "pure_j_off_diag" in results
    assert "mixed_j_anticomm" in results

    # Spot-check calibration
    cal = results["calibration"]
    assert cal["common_t"]["status"] == "CERTIFIED_IDENTICALLY"
    assert cal["dual_sdp"]["status"] == "CERTIFIED_STRICT_SDP"
    assert cal["gram_tester"]["status"] == "CERTIFIED_GRAM_TESTER"

    # Spot-check M05, pure-J, and mixed (J, {I2, F, G})
    assert results["m05_t_half"]["gram_tester"]["excludes_s_below_one"] is True
    assert results["m05_t_third"]["gram_tester"]["excludes_s_below_one"] is True
    assert results["pure_j_off_diag"]["gram_tester"]["excludes_s_below_one"] is True
    assert results["mixed_j_anticomm"]["gram_tester"]["excludes_s_below_one"] is True


def test_tamper_rejection():
    """Verify that corrupt or invalid certificates/pairs are strictly rejected."""
    K, Y, A, T = make_calibration_pair()

    # 1. Non-symmetric T
    T_corrupt = RationalMatrix([list(row) for row in T.data])
    T_corrupt.data[0][1] = Fraction(1)
    with pytest.raises(ValueError, match="not a valid anticommuting involution"):
        certify_common_t_involution(K, Y, T_corrupt, A)

    # 2. Non-involutive T (T^2 != I)
    T_scaled = T * Fraction(2)
    with pytest.raises(ValueError, match="not a valid anticommuting involution"):
        certify_common_t_involution(K, Y, T_scaled, A)

    # 3. Non-anticommuting T
    I6 = RationalMatrix.identity(6)
    with pytest.raises(ValueError, match="not a valid anticommuting involution"):
        certify_common_t_involution(K, Y, I6, A)

    # 4. Incompatible pair (Card M05 scalar product swap obstruction)
    # K = diag(J, 2J, J/2), Y = diag(J, J/2, 2J) has m_j = 0 but is mathematically incompatible
    k_incomp = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    y_incomp = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    for idx, w in enumerate([1, 2, Fraction(1, 2)]):
        k_incomp[2 * idx][2 * idx + 1] = Fraction(w)
        k_incomp[2 * idx + 1][2 * idx] = Fraction(-w)
    for idx, w in enumerate([1, Fraction(1, 2), 2]):
        y_incomp[2 * idx][2 * idx + 1] = Fraction(w)
        y_incomp[2 * idx + 1][2 * idx] = Fraction(-w)

    analysis_incomp = analyze_byers_nash_pair(RationalMatrix(k_incomp), RationalMatrix(y_incomp))
    assert analysis_incomp.is_compatible is False
    with pytest.raises(ValueError, match="Byers-Nash pair is incompatible"):
        certify_gram_tester_pair(RationalMatrix(k_incomp), RationalMatrix(y_incomp))
