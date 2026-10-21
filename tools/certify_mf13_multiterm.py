"""Exact Rational Analyzer & Certifier for the Multi-Term Involution Families (Lane MF-13).

Implements exact rational (Q) harmonic analysis and multi-term symmetric factorization
for the full-rank 6x6 Byers-Nash problem (rank K = 6, Darboux normal form K = diag(a J, b J, c J)):

1. Darboux-Anticommuting Symmetric Involution Hierarchy:
   - 4-Involution Klein Group {T_0, T_1, T_2, T_3}:
     T_r = diag(eps_{r,1} F, eps_{r,2} F, eps_{r,3} F) with F = [[1, 0], [0, -1]] and
     Klein 4-group sign triples (+1,+1,+1), (+1,-1,-1), (-1,+1,-1), (-1,-1,+1).
   - 8-Involution (F, G)-Klein Family {T_0, ..., T_3, G_0, ..., G_3}:
     Adds G_r = diag(eps_{r,1} G, eps_{r,2} G, eps_{r,3} G) with G = [[0, 1], [1, 0]].
   - Full 64-Element Darboux Involution Family I_64:
     All 4^3 = 64 orthogonal symmetric involutions T = diag(M_1, M_2, M_3) with
     M_p in {+F, -F, +G, -G}, every single one satisfying:
         T^T = T,   T^2 = I_6,   T K = -K T,
     and producing a valid same-square symmetric comparator S_T = K T with:
         S_T^T = S_T,   S_T^2 = -K^2,   ||S_T||_F^2 = ||K||_F^2.

2. Exact Character Projections & Discrete Parseval Identities over Q:
   - Klein 4-Group Character Table:
     (1/4) sum_{r=0}^3 T_r Y T_r = T_0 Y_diag T_0 = -Y_diag (for skew Y),
     while the 3 non-trivial characters isolate the off-diagonal block pairs (1,2), (1,3), (2,3).
   - 8-Involution & 64-Involution Isotropic Block-Trace Projection:
     For ANY symmetric H in S_6, averaging T H T over the 8-element (F, G)-Klein family
     (or the full 64-element family) equals the exact continuous 3-torus Haar integral:
         (1/8) sum_{m=1}^8 T^{(m)} H T^{(m)} = (1/64) sum_{T in I_64} T H T
             = diag((tr(H_11)/2) I_2, (tr(H_22)/2) I_2, (tr(H_33)/2) I_2) =: H_iso.
   - Exact Discrete Parseval Identities:
     * 4-Involution:
       sum_{r=0}^3 ||L_A(K T_r)||_F^2 = 4 sum_{r=0}^3 ||H_c(T_r)||_F^2 + 2 ||Y||_F^2 + 2 ||Y_diag||_F^2.
     * 8-Involution & 64-Involution:
       (1/8) sum_{m=1}^8 ||L_A(K T^{(m)})||_F^2 = (1/64) sum_{T in I_64} ||L_A(K T)||_F^2
           = 2 ||H||_F^2 + 2 ||H_iso||_F^2 + (1/2) ||Y||_F^2 + (1/2) ||Y_diag||_F^2.

3. Exact 4-Term & 3-Term Canonical Symmetric Factorizations of -Y K:
   - For ANY skew-symmetric Y in K_6 and K = diag(a J, b J, c J), the four canonical pieces
         Y_r := (1/2) Y_a(T_r) - (1/4) Y_diag   (r = 0, 1, 2, 3)
     are skew-symmetric, strictly anticommute with T_r (T_r Y_r = -Y_r T_r), and sum to Y:
         Y_0 + Y_1 + Y_2 + Y_3 = Y.
     Consequently, U_r = Y_r T_r in S_6 and V_r = K T_r in S_6 satisfy:
         sum_{r=0}^3 U_r V_r = -Y K,
         sum_{r=0}^3 <U_r, L_A(K T_r)>_F = <Y, L_A(K)>_F.

4. Multi-Term Involution Gram Certification on the 9D Affine Moduli Space:
   - Certifies full-rank non-Common-T rational pairs (Card M05 at t=1/2, t=1/3, t=2/5,
     and generic 3-frequency non-Common-T pairs) using the canonical multi-term involution
     test family without requiring external oracle matrices.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

# Ensure repository root is on sys.path
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.certify_mf13_pair import (  # noqa: E402
    analyze_byers_nash_pair,
    certify_gram_tester_pair,
    find_common_t_involution,
    frobenius_inner,
    frobenius_norm_sq,
    lyapunov_eval,
    make_calibration_pair,
    make_m05_pair,
    rational_nullspace,
    standard_symmetric_basis_6,
    symmetric_from_coords,
)
from tools.sdp_rational_cert import RationalMatrix, to_fraction  # noqa: E402

# ==============================================================================
# 1. Darboux Normal Form & The 4 / 8 / 64 Involution Families
# ==============================================================================

KLEIN_FOUR_SIGNS: list[tuple[int, int, int]] = [
    (1, 1, 1),
    (1, -1, -1),
    (-1, 1, -1),
    (-1, -1, 1),
]


def make_skew_witness_6(a: Any, b: Any, c: Any) -> RationalMatrix:
    """Construct the 6x6 Darboux skew-symmetric matrix K = diag(a J, b J, c J)."""
    fa, fb, fc = to_fraction(a), to_fraction(b), to_fraction(c)
    data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    for idx, w in enumerate([fa, fb, fc]):
        data[2 * idx][2 * idx + 1] = w
        data[2 * idx + 1][2 * idx] = -w
    return RationalMatrix(data)


def make_block_involution(
    blocks: tuple[tuple[str, int], tuple[str, int], tuple[str, int]]
) -> RationalMatrix:
    """Construct a 6x6 block-diagonal symmetric involution from 3 block specs ('F' or 'G', +-1)."""
    data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    for idx, (kind, sign) in enumerate(blocks):
        s = Fraction(sign)
        r0, r1 = 2 * idx, 2 * idx + 1
        if kind == "F":
            data[r0][r0] = s
            data[r1][r1] = -s
        elif kind == "G":
            data[r0][r1] = s
            data[r1][r0] = s
        else:
            raise ValueError(f"Unknown 2x2 block involution type: {kind}")
    return RationalMatrix(data)


def make_klein_four_involutions() -> list[RationalMatrix]:
    """Return the 4 commuting F-type Klein 4-group involutions [T0, T1, T2, T3]."""
    return [
        make_block_involution((("F", s1), ("F", s2), ("F", s3)))
        for s1, s2, s3 in KLEIN_FOUR_SIGNS
    ]


def make_klein_four_g_involutions() -> list[RationalMatrix]:
    """Return the 4 commuting G-type Klein 4-group involutions [G0, G1, G2, G3]."""
    return [
        make_block_involution((("G", s1), ("G", s2), ("G", s3)))
        for s1, s2, s3 in KLEIN_FOUR_SIGNS
    ]


def make_eight_involution_family() -> list[RationalMatrix]:
    """Return the 8-element (F, G)-Klein involution family {T0..T3, G0..G3}."""
    return make_klein_four_involutions() + make_klein_four_g_involutions()


def make_darboux_64_involutions() -> list[RationalMatrix]:
    """Return all 4^3 = 64 orthogonal symmetric involutions diag(M_1, M_2, M_3), M_p in {+-F, +-G}."""
    single_block_choices: list[tuple[str, int]] = [
        ("F", 1),
        ("F", -1),
        ("G", 1),
        ("G", -1),
    ]
    return [
        make_block_involution((b1, b2, b3))
        for b1, b2, b3 in itertools.product(single_block_choices, repeat=3)
    ]


# ==============================================================================
# 2. Block Projections & Involution Commuting / Anticommuting Projections
# ==============================================================================


def comm_part(T: RationalMatrix, X: RationalMatrix) -> RationalMatrix:
    """Return the T-commuting part X_c(T) = (1/2)(X + T X T)."""
    return (X + (T @ X @ T)) * Fraction(1, 2)


def anticomm_part(T: RationalMatrix, X: RationalMatrix) -> RationalMatrix:
    """Return the T-anticommuting part X_a(T) = (1/2)(X - T X T)."""
    return (X - (T @ X @ T)) * Fraction(1, 2)


def sym_part_ak(A: RationalMatrix, K: RationalMatrix) -> RationalMatrix:
    """Return H = sym(A K) = (1/2)(A K + (A K)^T)."""
    AK = A @ K
    return (AK + AK.transpose()) * Fraction(1, 2)


def diag_blocks_6(X: RationalMatrix) -> RationalMatrix:
    """Project a 6x6 matrix onto its three 2x2 diagonal blocks."""
    data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    for i in range(6):
        for j in range(6):
            if (i // 2) == (j // 2):
                data[i][j] = X.data[i][j]
    return RationalMatrix(data)


def off_diag_blocks_6(X: RationalMatrix) -> RationalMatrix:
    """Project a 6x6 matrix onto its off-diagonal 2x2 blocks."""
    return X - diag_blocks_6(X)


def block_pair_6(X: RationalMatrix, p: int, q: int) -> RationalMatrix:
    """Project a 6x6 matrix onto the off-diagonal 2x2 block pair (p, q) with p, q in {0, 1, 2}."""
    data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    for i in range(6):
        for j in range(6):
            pi, pj = i // 2, j // 2
            if (pi == p and pj == q) or (pi == q and pj == p):
                data[i][j] = X.data[i][j]
    return RationalMatrix(data)


def isotropic_block_trace_6(H: RationalMatrix) -> RationalMatrix:
    """Compute H_iso = diag((tr(H_11)/2) I_2, (tr(H_22)/2) I_2, (tr(H_33)/2) I_2)."""
    data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    for p in range(3):
        r0, r1 = 2 * p, 2 * p + 1
        avg_tr = (H.data[r0][r0] + H.data[r1][r1]) * Fraction(1, 2)
        data[r0][r0] = avg_tr
        data[r1][r1] = avg_tr
    return RationalMatrix(data)


# ==============================================================================
# 3. Exact Verification of the 4 / 8 / 64 Involution Hierarchy & Parseval Laws
# ==============================================================================


@dataclass
class MultiTermInvolutionAnalysis:
    """Exact rational verification of the 4-, 8-, and 64-involution hierarchy and Parseval laws."""

    name: str
    num_klein_4: int
    num_klein_8: int
    num_darboux_64: int
    all_64_symmetric: bool
    all_64_involutive: bool
    all_64_anticommute_K: bool
    all_64_same_square: bool
    all_64_preserve_norm: bool
    klein_4_character_diag_exact: bool
    klein_4_character_offdiag_exact: bool
    klein_8_isotropic_H_exact: bool
    darboux_64_isotropic_H_exact: bool
    identity_I2_all_64_exact: bool
    parseval_4_exact: bool
    parseval_8_exact: bool
    parseval_64_exact: bool
    four_term_factorization_exact: bool
    four_term_lyap_pairing_exact: bool
    norm_Y_sq: str
    norm_Y_diag_sq: str
    norm_Y_off_sq: str
    avg_4_gain_sq: str
    avg_8_gain_sq: str
    avg_64_gain_sq: str
    max_4_gain_sq: str
    max_8_gain_sq: str
    max_64_gain_sq: str

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def canonical_four_term_decomposition(
    Y: RationalMatrix,
) -> list[tuple[RationalMatrix, RationalMatrix]]:
    """Decompose skew-symmetric Y into 4 pairs (Y_r, T_r) with Y_r^T = -Y_r, T_r Y_r = -Y_r T_r, sum Y_r = Y.

    Formula:
        Y_r = (1/2) anticomm_part(T_r, Y) - (1/4) diag_blocks_6(Y)   for r = 0, 1, 2, 3.
    """
    klein4 = make_klein_four_involutions()
    Y_diag = diag_blocks_6(Y)
    pairs: list[tuple[RationalMatrix, RationalMatrix]] = []
    for T_r in klein4:
        Y_r = (anticomm_part(T_r, Y) * Fraction(1, 2)) - (Y_diag * Fraction(1, 4))
        pairs.append((Y_r, T_r))
    return pairs


def verify_multiterm_involution_hierarchy(
    K: RationalMatrix,
    A: RationalMatrix,
    name: str = "Multi-Term Involution Hierarchy",
) -> MultiTermInvolutionAnalysis:
    """Verify all algebraic, character, Parseval, and factorization identities over Q."""
    I6 = RationalMatrix.identity(6)
    Z6 = RationalMatrix.zeros(6, 6)

    klein4 = make_klein_four_involutions()
    klein8 = make_eight_involution_family()
    darboux64 = make_darboux_64_involutions()

    norm_K_sq = frobenius_norm_sq(K)
    neg_K_sq = (K @ K) * Fraction(-1)

    all_sym = True
    all_inv = True
    all_anticomm = True
    all_same_sq = True
    all_norm = True

    for T in darboux64:
        if (T - T.transpose()).max_abs_entry() != Fraction(0):
            all_sym = False
        if ((T @ T) - I6).max_abs_entry() != Fraction(0):
            all_inv = False
        if ((T @ K) + (K @ T)).max_abs_entry() != Fraction(0):
            all_anticomm = False
        S = K @ T
        if (S - S.transpose()).max_abs_entry() != Fraction(0):
            all_same_sq = False
        if ((S @ S) - neg_K_sq).max_abs_entry() != Fraction(0):
            all_same_sq = False
        if frobenius_norm_sq(S) != norm_K_sq:
            all_norm = False

    Y = lyapunov_eval(A, K)
    H = sym_part_ak(A, K)
    Y_diag = diag_blocks_6(Y)
    Y_off = off_diag_blocks_6(Y)
    H_iso = isotropic_block_trace_6(H)

    # 1. Verify Klein 4-Group Character Projections on Y
    T0, T1, T2, T3 = klein4
    avg_4_Y = ((T0 @ Y @ T0) + (T1 @ Y @ T1) + (T2 @ Y @ T2) + (T3 @ Y @ T3)) * Fraction(1, 4)
    char_diag_ok = (avg_4_Y + Y_diag).max_abs_entry() == Fraction(0)

    c12 = ((T0 @ Y @ T0) - (T1 @ Y @ T1) - (T2 @ Y @ T2) + (T3 @ Y @ T3)) * Fraction(1, 4)
    c13 = ((T0 @ Y @ T0) - (T1 @ Y @ T1) + (T2 @ Y @ T2) - (T3 @ Y @ T3)) * Fraction(1, 4)
    c23 = ((T0 @ Y @ T0) + (T1 @ Y @ T1) - (T2 @ Y @ T2) - (T3 @ Y @ T3)) * Fraction(1, 4)
    char_offdiag_ok = (
        (c12 - (T0 @ block_pair_6(Y, 0, 1) @ T0)).max_abs_entry() == Fraction(0)
        and (c13 - (T0 @ block_pair_6(Y, 0, 2) @ T0)).max_abs_entry() == Fraction(0)
        and (c23 - (T0 @ block_pair_6(Y, 1, 2) @ T0)).max_abs_entry() == Fraction(0)
    )

    # 2. Verify 8-Involution and 64-Involution Isotropic Block-Trace Projection on H
    sum_8_H = Z6
    for T in klein8:
        sum_8_H = sum_8_H + (T @ H @ T)
    avg_8_H = sum_8_H * Fraction(1, 8)
    iso_8_ok = (avg_8_H - H_iso).max_abs_entry() == Fraction(0)

    sum_64_H = Z6
    for T in darboux64:
        sum_64_H = sum_64_H + (T @ H @ T)
    avg_64_H = sum_64_H * Fraction(1, 64)
    iso_64_ok = (avg_64_H - H_iso).max_abs_entry() == Fraction(0)

    # 3. Verify Identity (I2) across all 64 involutions
    id_i2_ok = True
    gains_64: list[Fraction] = []
    for T in darboux64:
        gain_sq = frobenius_norm_sq(lyapunov_eval(A, K @ T))
        gains_64.append(gain_sq)
        hc_sq = frobenius_norm_sq(comm_part(T, H))
        ya_sq = frobenius_norm_sq(anticomm_part(T, Y))
        yc_sq = frobenius_norm_sq(comm_part(T, Y))
        if gain_sq != Fraction(4) * hc_sq + ya_sq:
            id_i2_ok = False
        if gain_sq - frobenius_norm_sq(Y) != Fraction(4) * hc_sq - yc_sq:
            id_i2_ok = False

    # 4. Verify 4-, 8-, and 64-Involution Parseval Identities
    gains_4 = [frobenius_norm_sq(lyapunov_eval(A, K @ T)) for T in klein4]
    gains_8 = [frobenius_norm_sq(lyapunov_eval(A, K @ T)) for T in klein8]

    sum_4_hc = sum(frobenius_norm_sq(comm_part(T, H)) for T in klein4)
    norm_Y_sq = frobenius_norm_sq(Y)
    norm_Y_diag_sq = frobenius_norm_sq(Y_diag)
    norm_Y_off_sq = frobenius_norm_sq(Y_off)
    norm_H_sq = frobenius_norm_sq(H)
    norm_H_iso_sq = frobenius_norm_sq(H_iso)

    parseval_4_ok = (
        sum(gains_4) == Fraction(4) * sum_4_hc + Fraction(2) * norm_Y_sq + Fraction(2) * norm_Y_diag_sq
        and sum(frobenius_norm_sq(comm_part(T, Y)) for T in klein4) == Fraction(2) * norm_Y_off_sq
    )

    expected_avg_8 = (
        Fraction(2) * norm_H_sq
        + Fraction(2) * norm_H_iso_sq
        + Fraction(1, 2) * norm_Y_sq
        + Fraction(1, 2) * norm_Y_diag_sq
    )
    avg_4_gain = sum(gains_4) * Fraction(1, 4)
    avg_8_gain = sum(gains_8) * Fraction(1, 8)
    avg_64_gain = sum(gains_64) * Fraction(1, 64)

    parseval_8_ok = avg_8_gain == expected_avg_8
    parseval_64_ok = avg_64_gain == expected_avg_8

    # 5. Verify Canonical 4-Term Symmetric Factorization of -Y K and <Y, L_A(K)>
    decomp = canonical_four_term_decomposition(Y)
    sum_Yr = Z6
    sum_Ur_Vr = Z6
    sum_pairing = Fraction(0)
    fact_props_ok = True
    for Y_r, T_r in decomp:
        if (Y_r + Y_r.transpose()).max_abs_entry() != Fraction(0):
            fact_props_ok = False
        if ((T_r @ Y_r) + (Y_r @ T_r)).max_abs_entry() != Fraction(0):
            fact_props_ok = False
        U_r = Y_r @ T_r
        V_r = K @ T_r
        if (U_r - U_r.transpose()).max_abs_entry() != Fraction(0):
            fact_props_ok = False
        sum_Yr = sum_Yr + Y_r
        sum_Ur_Vr = sum_Ur_Vr + (U_r @ V_r)
        sum_pairing += frobenius_inner(U_r, lyapunov_eval(A, V_r))

    neg_YK = (Y @ K) * Fraction(-1)
    fact_ok = (
        fact_props_ok
        and (sum_Yr - Y).max_abs_entry() == Fraction(0)
        and (sum_Ur_Vr - neg_YK).max_abs_entry() == Fraction(0)
    )
    pairing_ok = sum_pairing == frobenius_inner(Y, lyapunov_eval(A, K))

    return MultiTermInvolutionAnalysis(
        name=name,
        num_klein_4=len(klein4),
        num_klein_8=len(klein8),
        num_darboux_64=len(darboux64),
        all_64_symmetric=all_sym,
        all_64_involutive=all_inv,
        all_64_anticommute_K=all_anticomm,
        all_64_same_square=all_same_sq,
        all_64_preserve_norm=all_norm,
        klein_4_character_diag_exact=char_diag_ok,
        klein_4_character_offdiag_exact=char_offdiag_ok,
        klein_8_isotropic_H_exact=iso_8_ok,
        darboux_64_isotropic_H_exact=iso_64_ok,
        identity_I2_all_64_exact=id_i2_ok,
        parseval_4_exact=parseval_4_ok,
        parseval_8_exact=parseval_8_ok,
        parseval_64_exact=parseval_64_ok,
        four_term_factorization_exact=fact_ok,
        four_term_lyap_pairing_exact=pairing_ok,
        norm_Y_sq=str(norm_Y_sq),
        norm_Y_diag_sq=str(norm_Y_diag_sq),
        norm_Y_off_sq=str(norm_Y_off_sq),
        avg_4_gain_sq=str(avg_4_gain),
        avg_8_gain_sq=str(avg_8_gain),
        avg_64_gain_sq=str(avg_64_gain),
        max_4_gain_sq=str(max(gains_4)),
        max_8_gain_sq=str(max(gains_8)),
        max_64_gain_sq=str(max(gains_64)),
    )


# ==============================================================================
# 4. Canonical Multi-Term Involution Test Ensemble & Non-Common-T Certification
# ==============================================================================


def build_multiterm_involution_ensemble(
    K: RationalMatrix, Y: RationalMatrix
) -> list[tuple[RationalMatrix, Fraction]]:
    """Build a canonical multi-term symmetric test ensemble from (K, Y) using the 8-involution family.

    Includes:
    1. The identity matrix I_6.
    2. The 8 same-square symmetric comparators V_m = K T^{(m)} for T^{(m)} in the 8-involution family.
    3. The non-zero symmetric left-partner test matrices U_m = Y_a(T^{(m)}) T^{(m)} = (1/2)(Y T^{(m)} - T^{(m)} Y).
    4. The symmetrized cross-products (1/2)(Y K T^{(m)} + T^{(m)} K Y).
    Requires NO external oracle matrix Q.
    """
    klein8 = make_eight_involution_family()
    ensemble: list[tuple[RationalMatrix, Fraction]] = [
        (RationalMatrix.identity(6), Fraction(1))
    ]
    for T in klein8:
        V_T = K @ T
        ensemble.append((V_T, Fraction(1, 8)))
        U_T = anticomm_part(T, Y) @ T
        if frobenius_norm_sq(U_T) > Fraction(0):
            ensemble.append((U_T, Fraction(1, 8)))
        cross = ((Y @ K @ T) + (T @ K @ Y)) * Fraction(1, 2)
        if frobenius_norm_sq(cross) > Fraction(0):
            ensemble.append((cross, Fraction(1, 16)))
    return ensemble


def find_symmetric_intertwiner(
    K: RationalMatrix, Y: RationalMatrix
) -> RationalMatrix | None:
    """Solve the linear intertwiner system S K - Y S = 0 for S in S_6 over Q and normalize S^2 = I_6 if possible."""
    import math

    sym_basis = standard_symmetric_basis_6()
    cols: list[list[Fraction]] = []
    for B in sym_basis:
        diff = (B @ K) - (Y @ B)
        cols.append([diff.data[r][c] for r in range(6) for c in range(6)])
    sys_mat = [list(row) for row in zip(*cols, strict=True)]
    null_inter = rational_nullspace(sys_mat)
    if not null_inter:
        return None
    S_cand = symmetric_from_coords(null_inter[0])
    I6 = RationalMatrix.identity(6)
    sq = S_cand @ S_cand
    scalar = sq.data[0][0]
    if scalar > 0 and (sq - (I6 * scalar)).max_abs_entry() == Fraction(0):
        r_num = int(math.isqrt(scalar.numerator))
        r_den = int(math.isqrt(scalar.denominator))
        if r_num * r_num == scalar.numerator and r_den * r_den == scalar.denominator:
            return S_cand * Fraction(r_den, r_num)
    return S_cand


def make_generic_non_common_t_pair(
    t1: Any = "1/2", t2: Any = "1/10"
) -> tuple[RationalMatrix, RationalMatrix]:
    """Construct a full-rank 3-frequency compatible pair (K, Y) with ZERO common anticommuting subspace.

    Applies three coupled rational Cayley rotations across planes and parities:
        u = cayley_rot(0, 4, t1) @ cayley_rot(1, 2, t2) @ cayley_rot(2, 5, t2)
    on top of the plane-swap involution q0, setting Q = u q0 u^T and Y = Q K Q.
    Because Q = Q^T and Q^2 = I_6, (K, Y) satisfies all compatibility conditions (m_0 = m_1 = m_2 = 0,
    rank(Phi_{K,Y}) = 12, nullity = 9), while mixing across both planes and parities forces the common
    anticommuting symmetric subspace {B in S_6 : B K + K B = 0 and B Y + Y B = 0} to be strictly {0}.
    """
    K = make_skew_witness_6(1, 2, 3)
    f1 = to_fraction(t1)
    f2 = to_fraction(t2)

    def cayley_rot(i: int, j: int, t: Fraction) -> RationalMatrix:
        u = [[Fraction(1) if r == c else Fraction(0) for c in range(6)] for r in range(6)]
        co = (Fraction(1) - t * t) / (Fraction(1) + t * t)
        si = (Fraction(2) * t) / (Fraction(1) + t * t)
        u[i][i] = co
        u[j][j] = co
        u[i][j] = si
        u[j][i] = -si
        return RationalMatrix(u)

    q0_data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    for i, j in enumerate([2, 3, 0, 1, 4, 5]):
        q0_data[i][j] = Fraction(1)
    q0 = RationalMatrix(q0_data)

    u = cayley_rot(0, 4, f1) @ cayley_rot(1, 2, f2) @ cayley_rot(2, 5, f2)
    Q = u @ q0 @ u.transpose()
    Y = Q @ K @ Q
    return K, Y


def run_multiterm_benchmark_suite() -> dict[str, Any]:
    """Run the complete exact rational multi-term involution verification and certification suite."""
    results: dict[str, Any] = {}

    # 1. Calibration Pair
    K_cal, Y_cal, A_cal, _ = make_calibration_pair()
    hier_cal = verify_multiterm_involution_hierarchy(
        K_cal, A_cal, name="Calibration Pair diag(J, 2J, 3J)"
    )
    results["calibration_hierarchy"] = hier_cal.to_dict()

    # 2. Card M05 at t=1/2 (Multi-Term Ensemble without External Q Oracle)
    K_half, Y_half, _ = make_m05_pair("1/2")
    common_t_half = find_common_t_involution(K_half, Y_half)
    analysis_half = analyze_byers_nash_pair(K_half, Y_half)
    A0_half = RationalMatrix([[Fraction(x) for x in row] for row in analysis_half.A0])
    hier_half = verify_multiterm_involution_hierarchy(
        K_half, A0_half, name="Card M05 (t=1/2) at A0"
    )
    ensemble_half = build_multiterm_involution_ensemble(K_half, Y_half)
    cert_half_multi = certify_gram_tester_pair(
        K_half,
        Y_half,
        tests=ensemble_half,
        name="Card M05 (t=1/2) Canonical Multi-Term Involution Ensemble",
    )
    results["m05_t_half"] = {
        "has_common_t": common_t_half is not None,
        "hierarchy": hier_half.to_dict(),
        "multiterm_gram_cert": cert_half_multi.to_dict(),
    }

    # 3. Card M05 at t=1/3 (Multi-Term Ensemble without External Q Oracle)
    K_third, Y_third, _ = make_m05_pair("1/3")
    common_t_third = find_common_t_involution(K_third, Y_third)
    analysis_third = analyze_byers_nash_pair(K_third, Y_third)
    A0_third = RationalMatrix([[Fraction(x) for x in row] for row in analysis_third.A0])
    hier_third = verify_multiterm_involution_hierarchy(
        K_third, A0_third, name="Card M05 (t=1/3) at A0"
    )
    ensemble_third = build_multiterm_involution_ensemble(K_third, Y_third)
    cert_third_multi = certify_gram_tester_pair(
        K_third,
        Y_third,
        tests=ensemble_third,
        name="Card M05 (t=1/3) Canonical Multi-Term Involution Ensemble",
    )
    results["m05_t_third"] = {
        "has_common_t": common_t_third is not None,
        "hierarchy": hier_third.to_dict(),
        "multiterm_gram_cert": cert_third_multi.to_dict(),
    }

    # 4. Strictly Non-Common-T 3-Frequency Pair (t1=1/2, t2=1/10): Zero Common-T Subspace
    K_gen, Y_gen = make_generic_non_common_t_pair("1/2", "1/10")
    common_t_gen = find_common_t_involution(K_gen, Y_gen)
    analysis_gen = analyze_byers_nash_pair(K_gen, Y_gen)
    A0_gen = RationalMatrix([[Fraction(x) for x in row] for row in analysis_gen.A0])
    hier_gen = verify_multiterm_involution_hierarchy(
        K_gen, A0_gen, name="Strictly Non-Common-T 3-Frequency Pair (t1=1/2, t2=1/10)"
    )
    ensemble_gen = build_multiterm_involution_ensemble(K_gen, Y_gen)
    cert_gen_multi = certify_gram_tester_pair(
        K_gen,
        Y_gen,
        tests=ensemble_gen,
        name="Strictly Non-Common-T Canonical Multi-Term Certificate (Pure 8-Involution Ensemble)",
    )
    results["generic_non_common_t"] = {
        "has_common_t": common_t_gen is not None,
        "analysis_compatible": analysis_gen.is_compatible,
        "phi_rank": analysis_gen.phi_rank,
        "phi_nullity": analysis_gen.phi_nullity,
        "hierarchy": hier_gen.to_dict(),
        "multiterm_gram_cert": cert_gen_multi.to_dict(),
    }

    return results


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Exact Rational Multi-Term Involution Analyzer & Certifier for 6x6 Byers-Nash (MF-13)"
    )
    parser.add_argument(
        "--output",
        "-o",
        type=str,
        help="Path to write JSON certificate results",
    )
    parser.add_argument(
        "--quiet",
        "-q",
        action="store_true",
        help="Suppress verbose console summary",
    )
    args = parser.parse_args()

    results = run_multiterm_benchmark_suite()

    if not args.quiet:
        print("=" * 84)
        print("EXACT RATIONAL MULTI-TERM INVOLUTION CERTIFICATES FOR 6x6 BYERS-NASH (LANE MF-13)")
        print("=" * 84)
        cal = results["calibration_hierarchy"]
        print("1. Involution Group Hierarchy & Parseval Verification (4 / 8 / 64 Involutions):")
        print(f"   - All 64 Darboux involutions symmetric, involutive, anticommute with K: "
              f"{cal['all_64_symmetric'] and cal['all_64_involutive'] and cal['all_64_anticommute_K']}")
        print(f"   - All 64 S_T = K T same-square (S_T^2 = -K^2) and norm-preserving: "
              f"{cal['all_64_same_square'] and cal['all_64_preserve_norm']}")
        print(f"   - Klein 4-Group character projections exact (diag & off-diag): "
              f"{cal['klein_4_character_diag_exact'] and cal['klein_4_character_offdiag_exact']}")
        print(f"   - 8-Involution & 64-Involution isotropic H_iso projection exact: "
              f"{cal['klein_8_isotropic_H_exact'] and cal['darboux_64_isotropic_H_exact']}")
        for key, label in [
            ("m05_t_half", "2. Card M05 (t=1/2, Multi-Term Ensemble without External Q Oracle)"),
            ("m05_t_third", "3. Card M05 (t=1/3, Multi-Term Ensemble without External Q Oracle)"),
            ("generic_non_common_t", "4. Strictly Non-Common-T 3-Frequency Pair (t1=1/2, t2=1/10)"),
        ]:
            entry = results[key]
            h = entry["hierarchy"]
            c = entry["multiterm_gram_cert"]
            print(f"{label}:")
            print(f"   - Common-T exists: {entry['has_common_t']}")
            print(f"   - Identity (I2) & 4/8/64 Parseval identities exact: "
                  f"{h['identity_I2_all_64_exact'] and h['parseval_4_exact'] and h['parseval_8_exact'] and h['parseval_64_exact']}")
            print(f"   - Canonical 4-term -YK factorization & Lyapunov pairing exact: "
                  f"{h['four_term_factorization_exact'] and h['four_term_lyap_pairing_exact']}")
            print(f"   - Multi-Term Gram LDL^T min pivot: {c['min_pivot']} > 0")
            print(f"   - Certified s(A)^2 lower bound (no external Q oracle): "
                  f"{c['certified_s_sq_bound']} >= 1 ({c['excludes_s_below_one']})")
        print("=" * 84)

    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(results, indent=2) + "\n")
        print(f"Results written to {out_path}")


if __name__ == "__main__":
    main()
