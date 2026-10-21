"""Tests for the exact rational Multi-Term Involution Analyzer & Certifier (Lane MF-13).

Verifies:
1. Full 64-element Darboux-anticommuting symmetric involution group I_64:
   - T^T = T, T^2 = I_6, T K = -K T
   - S_T = K T symmetric, same-square S_T^2 = -K^2, and norm-preserving ||S_T||_F^2 = ||K||_F^2
2. Klein 4-Group {T_0, T_1, T_2, T_3} character projections isolating Y_diag and the 3 off-diagonal block pairs
3. 8-Involution (F, G)-Klein and 64-Involution isotropic block-trace projection H_iso on symmetric H in S_6
4. Identity (I2) and 4-, 8-, and 64-Involution discrete Parseval identities over Q
5. Canonical 4-Term symmetric factorization of -Y K and Lyapunov pairing <Y, L_A(K)>_F
6. Multi-term involution Gram LDL^T > 0 certification on Card M05 (t=1/2, t=1/3) and
   strictly non-Common-T 3-frequency compatible pairs (where find_common_t_involution is None)
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.certify_mf13_multiterm import (  # noqa: E402
    NON_COMMON_T_GRID_PARAMS,
    anticomm_part,
    block_pair_6,
    build_multiterm_involution_ensemble,
    canonical_four_term_decomposition,
    certify_non_common_t_grid,
    comm_part,
    diag_blocks_6,
    find_symmetric_intertwiner,
    isotropic_block_trace_6,
    make_darboux_64_involutions,
    make_eight_involution_family,
    make_generic_non_common_t_pair,
    make_klein_four_involutions,
    make_skew_witness_6,
    off_diag_blocks_6,
    run_multiterm_benchmark_suite,
    sym_part_ak,
    verify_eight_involution_dominance_and_intertwiner,
    verify_multiterm_involution_hierarchy,
)
from tools.certify_mf13_pair import (
    analyze_byers_nash_pair,
    certify_gram_tester_pair,
    find_common_t_involution,
    frobenius_inner,
    frobenius_norm_sq,
    lyapunov_eval,
    make_calibration_pair,
    make_m05_pair,
)
from tools.sdp_rational_cert import RationalMatrix, verify_ldl_identity


def test_darboux_64_involution_group_and_same_square() -> None:
    """Verify all 64 Darboux involutions anticommute with K = diag(aJ, bJ, cJ) and have S_T^2 = -K^2."""
    K = make_skew_witness_6(2, 5, 7)
    I6 = RationalMatrix.identity(6)
    neg_K_sq = (K @ K) * Fraction(-1)
    norm_K_sq = frobenius_norm_sq(K)

    darboux64 = make_darboux_64_involutions()
    assert len(darboux64) == 64

    for T in darboux64:
        assert (T - T.transpose()).max_abs_entry() == Fraction(0)
        assert ((T @ T) - I6).max_abs_entry() == Fraction(0)
        assert ((T @ K) + (K @ T)).max_abs_entry() == Fraction(0)

        S_T = K @ T
        assert (S_T - S_T.transpose()).max_abs_entry() == Fraction(0)
        assert ((S_T @ S_T) - neg_K_sq).max_abs_entry() == Fraction(0)
        assert frobenius_norm_sq(S_T) == norm_K_sq


def test_klein_four_group_commuting_and_character_projections() -> None:
    """Verify Klein 4-group multiplication table and exact character projections on Y in K_6."""
    klein4 = make_klein_four_involutions()
    assert len(klein4) == 4
    T0, T1, T2, T3 = klein4

    # Commuting group closure: T1*T2 = T0*T3, T1*T3 = T0*T2, T2*T3 = T0*T1
    for Ta in klein4:
        for Tb in klein4:
            assert ((Ta @ Tb) - (Tb @ Ta)).max_abs_entry() == Fraction(0)
    assert ((T1 @ T2) - (T0 @ T3)).max_abs_entry() == Fraction(0)
    assert ((T1 @ T3) - (T0 @ T2)).max_abs_entry() == Fraction(0)
    assert ((T2 @ T3) - (T0 @ T1)).max_abs_entry() == Fraction(0)

    # Generic skew-symmetric Y with all 15 upper-triangular entries distinct
    y_data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    val = 1
    for i in range(6):
        for j in range(i + 1, 6):
            y_data[i][j] = Fraction(val)
            y_data[j][i] = Fraction(-val)
            val += 1
    Y = RationalMatrix(y_data)

    Y_diag = diag_blocks_6(Y)
    Y_off = off_diag_blocks_6(Y)
    assert ((Y_diag + Y_off) - Y).max_abs_entry() == Fraction(0)
    assert frobenius_inner(Y_diag, Y_off) == Fraction(0)

    # Trivial character: (1/4) sum_{r=0}^3 T_r Y T_r = T0 Y_diag T0 = -Y_diag
    avg_4 = ((T0 @ Y @ T0) + (T1 @ Y @ T1) + (T2 @ Y @ T2) + (T3 @ Y @ T3)) * Fraction(1, 4)
    assert (avg_4 - (T0 @ Y_diag @ T0)).max_abs_entry() == Fraction(0)
    assert (avg_4 + Y_diag).max_abs_entry() == Fraction(0)

    # Non-trivial characters isolate off-diagonal block pairs (0,1), (0,2), (1,2)
    c01 = ((T0 @ Y @ T0) - (T1 @ Y @ T1) - (T2 @ Y @ T2) + (T3 @ Y @ T3)) * Fraction(1, 4)
    c02 = ((T0 @ Y @ T0) - (T1 @ Y @ T1) + (T2 @ Y @ T2) - (T3 @ Y @ T3)) * Fraction(1, 4)
    c12 = ((T0 @ Y @ T0) + (T1 @ Y @ T1) - (T2 @ Y @ T2) - (T3 @ Y @ T3)) * Fraction(1, 4)
    assert (c01 - (T0 @ block_pair_6(Y, 0, 1) @ T0)).max_abs_entry() == Fraction(0)
    assert (c02 - (T0 @ block_pair_6(Y, 0, 2) @ T0)).max_abs_entry() == Fraction(0)
    assert (c12 - (T0 @ block_pair_6(Y, 1, 2) @ T0)).max_abs_entry() == Fraction(0)

    # Parseval over Klein 4-group
    sum_comm_sq = sum(frobenius_norm_sq(comm_part(T, Y)) for T in klein4)
    sum_anti_sq = sum(frobenius_norm_sq(anticomm_part(T, Y)) for T in klein4)
    assert sum_comm_sq == Fraction(2) * frobenius_norm_sq(Y_off)
    assert sum_anti_sq == Fraction(2) * frobenius_norm_sq(Y) + Fraction(2) * frobenius_norm_sq(Y_diag)


def test_eight_and_64_involution_isotropic_projection() -> None:
    """Verify that averaging T H T over the 8-element or 64-element family gives H_iso."""
    h_data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    val = 1
    for i in range(6):
        for j in range(i, 6):
            h_data[i][j] = Fraction(val)
            h_data[j][i] = Fraction(val)
            val += 1
    H = RationalMatrix(h_data)
    H_iso = isotropic_block_trace_6(H)

    klein8 = make_eight_involution_family()
    darboux64 = make_darboux_64_involutions()
    assert len(klein8) == 8

    Z6 = RationalMatrix.zeros(6, 6)
    avg8 = Z6
    for T in klein8:
        avg8 = avg8 + (T @ H @ T)
    avg8 = avg8 * Fraction(1, 8)
    assert (avg8 - H_iso).max_abs_entry() == Fraction(0)

    avg64 = Z6
    for T in darboux64:
        avg64 = avg64 + (T @ H @ T)
    avg64 = avg64 * Fraction(1, 64)
    assert (avg64 - H_iso).max_abs_entry() == Fraction(0)

    # Norm identity: (1/8) sum ||H_c(T^{(m)})||_F^2 = (1/2) ||H||_F^2 + (1/2) ||H_iso||_F^2
    avg8_hc = sum(frobenius_norm_sq(comm_part(T, H)) for T in klein8) * Fraction(1, 8)
    avg64_hc = sum(frobenius_norm_sq(comm_part(T, H)) for T in darboux64) * Fraction(1, 64)
    expected = Fraction(1, 2) * frobenius_norm_sq(H) + Fraction(1, 2) * frobenius_norm_sq(H_iso)
    assert avg8_hc == expected
    assert avg64_hc == expected


def test_canonical_four_term_decomposition_and_lyapunov_pairing() -> None:
    """Verify exact 4-term decomposition of Y, -Y K, and <Y, L_A(K)>_F."""
    K, Y = make_generic_non_common_t_pair("1/2", "1/10")
    analysis = analyze_byers_nash_pair(K, Y)
    A0 = RationalMatrix([[Fraction(x) for x in row] for row in analysis.A0])

    decomp = canonical_four_term_decomposition(Y)
    assert len(decomp) == 4

    Z6 = RationalMatrix.zeros(6, 6)
    sum_Yr = Z6
    sum_Ur_Vr = Z6
    sum_pairing = Fraction(0)

    for Y_r, T_r in decomp:
        # Skew-symmetric and strictly anticommuting with T_r
        assert (Y_r + Y_r.transpose()).max_abs_entry() == Fraction(0)
        assert ((T_r @ Y_r) + (Y_r @ T_r)).max_abs_entry() == Fraction(0)

        U_r = Y_r @ T_r
        V_r = K @ T_r
        assert (U_r - U_r.transpose()).max_abs_entry() == Fraction(0)
        assert (V_r - V_r.transpose()).max_abs_entry() == Fraction(0)

        # Single-involution pairing on each piece: <U_r, L_A0(V_r)> = <Y_r, L_A0(K)>
        assert frobenius_inner(U_r, lyapunov_eval(A0, V_r)) == frobenius_inner(Y_r, lyapunov_eval(A0, K))

        sum_Yr = sum_Yr + Y_r
        sum_Ur_Vr = sum_Ur_Vr + (U_r @ V_r)
        sum_pairing += frobenius_inner(U_r, lyapunov_eval(A0, V_r))

    assert (sum_Yr - Y).max_abs_entry() == Fraction(0)
    assert (sum_Ur_Vr + (Y @ K)).max_abs_entry() == Fraction(0)
    assert sum_pairing == frobenius_inner(Y, lyapunov_eval(A0, K))
    assert sum_pairing == frobenius_norm_sq(Y)


def test_multiterm_hierarchy_and_non_common_t_certification() -> None:
    """Verify full hierarchy identities and Gram LDL^T > 0 certification on non-Common-T pairs."""
    # 1. Strictly non-Common-T pair (t1=1/2, t2=1/10)
    K_gen, Y_gen = make_generic_non_common_t_pair("1/2", "1/10")
    assert find_common_t_involution(K_gen, Y_gen) is None

    analysis = analyze_byers_nash_pair(K_gen, Y_gen)
    assert analysis.is_compatible is True
    assert analysis.trace_moments == ["0", "0", "0"]
    assert analysis.phi_rank == 12
    assert analysis.phi_nullity == 9

    A0 = RationalMatrix([[Fraction(x) for x in row] for row in analysis.A0])
    hier = verify_multiterm_involution_hierarchy(K_gen, A0)
    assert hier.all_64_symmetric is True
    assert hier.all_64_involutive is True
    assert hier.all_64_anticommute_K is True
    assert hier.all_64_same_square is True
    assert hier.all_64_preserve_norm is True
    assert hier.klein_4_character_diag_exact is True
    assert hier.klein_4_character_offdiag_exact is True
    assert hier.klein_8_isotropic_H_exact is True
    assert hier.darboux_64_isotropic_H_exact is True
    assert hier.identity_I2_all_64_exact is True
    assert hier.parseval_4_exact is True
    assert hier.parseval_8_exact is True
    assert hier.parseval_64_exact is True
    assert hier.four_term_factorization_exact is True
    assert hier.four_term_lyap_pairing_exact is True

    # Pure 8-involution multi-term Gram certificate (no external Q oracle, no intertwiner needed)
    ensemble = build_multiterm_involution_ensemble(K_gen, Y_gen)
    cert = certify_gram_tester_pair(K_gen, Y_gen, tests=ensemble)
    assert Fraction(cert.min_pivot) > 0
    assert Fraction(cert.certified_s_sq_bound) > Fraction(1)
    assert cert.excludes_s_below_one is True

    # Verify LDL^T identity directly
    G_mat = RationalMatrix([[Fraction(x) for x in row] for row in cert.Gram])
    L_mat = RationalMatrix([[Fraction(x) for x in row] for row in cert.L])
    D_vec = [Fraction(x) for x in cert.D]
    ok, max_err = verify_ldl_identity(L_mat, D_vec, G_mat)
    assert ok is True
    assert max_err == Fraction(0)

    # 2. Larger-angle non-Common-T pair (t1=1/2, t2=1/5) certified with solved linear intertwiner
    K_large, Y_large = make_generic_non_common_t_pair("1/2", "1/5")
    assert find_common_t_involution(K_large, Y_large) is None
    S_inter = find_symmetric_intertwiner(K_large, Y_large)
    assert S_inter is not None
    assert (S_inter - S_inter.transpose()).max_abs_entry() == Fraction(0)
    assert ((S_inter @ K_large) - (Y_large @ S_inter)).max_abs_entry() == Fraction(0)

    tests_large = [(RationalMatrix.identity(6), Fraction(1)), (S_inter, Fraction(1))]
    for T in make_eight_involution_family():
        tests_large.append((K_large @ T, Fraction(1, 256)))
    cert_large = certify_gram_tester_pair(K_large, Y_large, tests=tests_large)
    assert Fraction(cert_large.min_pivot) > 0
    assert Fraction(cert_large.certified_s_sq_bound) > Fraction(1)
    assert cert_large.excludes_s_below_one is True


def test_eight_involution_dominance_and_symmetric_intertwiner_grid_10() -> None:
    """Verify the 8-involution dominance corollary and 10-pair non-Common-T grid certification."""
    assert len(NON_COMMON_T_GRID_PARAMS) == 10
    grid_results = certify_non_common_t_grid()
    assert len(grid_results) == 10

    for entry in grid_results:
        assert entry["has_common_t"] is False
        assert Fraction(entry["min_pivot"]) > Fraction(0)
        assert Fraction(entry["certified_s_sq_bound"]) > Fraction(1)
        assert entry["excludes_s_below_one"] is True
        dom = entry["dominance_and_intertwiner"]
        assert dom["excess_identity_exact"] is True
        assert dom["implication_valid"] is True
        assert dom["intertwiner_found"] is True
        assert dom["intertwiner_duality_exact"] is True

    # Also verify on Calibration Pair where dominance condition 4||H||^2 + 4||H_iso||^2 >= ||Y_off||^2 holds
    K_cal, Y_cal, A_cal, _ = make_calibration_pair()
    dom_cal = verify_eight_involution_dominance_and_intertwiner(K_cal, Y_cal, A_cal)
    assert dom_cal["excess_identity_exact"] is True
    assert dom_cal["condition_holds"] is True
    assert dom_cal["max_8_dominates"] is True
    assert dom_cal["implication_valid"] is True


def test_run_multiterm_benchmark_suite() -> None:
    """Verify the full benchmark suite executes cleanly and all certificates pass."""
    results = run_multiterm_benchmark_suite()
    assert results["m05_t_half"]["multiterm_gram_cert"]["excludes_s_below_one"] is True
    assert results["m05_t_third"]["multiterm_gram_cert"]["excludes_s_below_one"] is True
    assert results["generic_non_common_t"]["has_common_t"] is False
    assert results["generic_non_common_t"]["multiterm_gram_cert"]["excludes_s_below_one"] is True
    assert len(results["non_common_t_grid_10"]) == 10
    assert all(r["excludes_s_below_one"] for r in results["non_common_t_grid_10"])

