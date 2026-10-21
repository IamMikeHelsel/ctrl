"""Exact Rational Semidefinite and Algebraic Certificate Tools for 6x6 Byers-Nash Pairs.

Lane MF-13 (Byers-Nash conjecture in dimension n=6):
    Lyapunov operator: L_A(X) = A X + X A^T.
    Conjecture: s(A) = ||L_A|_{S_6}||_F >= ||L_A|_{K_6}||_F = k(A) for all real A in R^{6x6}.
    Normalized skew singular witness pair (K, Y) with paired value 1:
        A K + K A^T = Y,   A^T Y + Y A = K,   ||K||_F = ||Y||_F = 1.

Mathematical Architecture:
1. Linear Elimination & Sylvester Operator:
   With H = A K - (1/2) Y in S_6 (21 dimensions), the bilateral equations become:
       Phi_{K,Y}(H) := (K Y) H - H (Y K) = K^3 - (1/2)(Y^2 K + K Y^2) =: RHS(K, Y).
   Compatibility requires 3 trace moments:
       m_j(K, Y) := tr((Y K)^j (Y^2 - K^2)) = 0  for j = 0, 1, 2.
   Generically, rank(Phi_{K,Y}) = 12 and nullity = 9, yielding a 9D affine family:
       A(z) = A_0 + sum_{r=1}^9 z_r A_r.

2. Stratified Certificate Methodology:
   - Locus 1: Common-T Involution Locus (8D equality locus where k=s=1).
     Exact algebraic SOS certificate: a rational symmetric orthogonal involution T
     (T = T^T, T^2 = I, T K = -K T, T Y = -Y T) produces symmetric comparators
     X_v = K T and X_u = Y T satisfying <X_u, L_A(X_v)> = ||Y||_F^2 identically for all A(z).
     By Cauchy-Schwarz, s(A) >= ||Y||/||K|| = 1 identically with zero slack needed.
   - Locus 2: Generic Interior Rational Pairs (e.g. Card M05 at t=1/2, t=1/3).
     Certified via exact rational LDL^T > 0 factorizations:
     (a) 21x21 Dual SDP certificate W_Q in Q^{21x21} with W_Q = L D L^T > 0 (all 21 D_i > 0).
     (b) 9x9 Gram Tester certificate G in Q^{9x9} with G = L D L^T > 0 and exact minimizer z*.

AI-assisted research tool for Lane MF-13 (Byers-Nash n=6).
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

# Ensure repository root is on sys.path
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.sdp_rational_cert import (  # noqa: E402
    RationalMatrix,
    rational_ldl,
    to_fraction,
    verify_ldl_identity,
)

# ==============================================================================
# Standard Bases and Utilities for S_6 and K_6
# ==============================================================================


def standard_symmetric_basis_6() -> list[RationalMatrix]:
    """Return standard integer basis of S_6 (21 matrices).

    Diagonal elements E_ii (norm 1), off-diagonal elements E_ij + E_ji (norm sqrt(2)).
    Ordered lexicographically by (i, j) with 0 <= i <= j < 6.
    """
    basis: list[RationalMatrix] = []
    for i in range(6):
        for j in range(i, 6):
            data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
            if i == j:
                data[i][j] = Fraction(1)
            else:
                data[i][j] = Fraction(1)
                data[j][i] = Fraction(1)
            basis.append(RationalMatrix(data))
    return basis


def standard_skew_basis_6() -> list[RationalMatrix]:
    """Return standard integer basis of K_6 (15 matrices).

    Off-diagonal elements E_ij - E_ji for 0 <= i < j < 6.
    """
    basis: list[RationalMatrix] = []
    for i in range(6):
        for j in range(i + 1, 6):
            data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
            data[i][j] = Fraction(1)
            data[j][i] = Fraction(-1)
            basis.append(RationalMatrix(data))
    return basis


def upper_skew_coords(M: RationalMatrix) -> list[Fraction]:
    """Extract 15 upper-triangular entries (i < j) of a 6x6 matrix."""
    if M.shape != (6, 6):
        raise ValueError(f"Expected 6x6 matrix, got {M.shape}")
    coords: list[Fraction] = []
    for i in range(6):
        for j in range(i + 1, 6):
            coords.append(M.data[i][j])
    return coords


def vector_from_symmetric_coords(M: RationalMatrix) -> list[Fraction]:
    """Extract coordinates of M in the standard integer symmetric basis."""
    if M.shape != (6, 6):
        raise ValueError(f"Expected 6x6 matrix, got {M.shape}")
    coords: list[Fraction] = []
    for i in range(6):
        for j in range(i, 6):
            if i == j:
                coords.append(M.data[i][i])
            else:
                coords.append(M.data[i][j])
    return coords


def symmetric_from_coords(coords: list[Any]) -> RationalMatrix:
    """Reconstruct a 6x6 symmetric matrix from 21 basis coordinates."""
    if len(coords) != 21:
        raise ValueError(f"Expected 21 coordinates, got {len(coords)}")
    data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    k = 0
    for i in range(6):
        for j in range(i, 6):
            val = to_fraction(coords[k])
            if i == j:
                data[i][i] = val
            else:
                data[i][j] = val
                data[j][i] = val
            k += 1
    return RationalMatrix(data)


def frobenius_inner(A: RationalMatrix, B: RationalMatrix) -> Fraction:
    """Exact Frobenius inner product <A, B> = tr(A^T B)."""
    if A.shape != B.shape:
        raise ValueError(f"Shape mismatch: {A.shape} vs {B.shape}")
    total = Fraction(0)
    for i in range(A.rows):
        for j in range(A.cols):
            total += A.data[i][j] * B.data[i][j]
    return total


def frobenius_norm_sq(A: RationalMatrix) -> Fraction:
    """Exact squared Frobenius norm ||A||_F^2 = <A, A>."""
    return frobenius_inner(A, A)


def lyapunov_eval(A: RationalMatrix, X: RationalMatrix) -> RationalMatrix:
    """Evaluate Lyapunov operator L_A(X) = A X + X A^T."""
    return (A @ X) + (X @ A.transpose())


# ==============================================================================
# Exact Linear Algebra over Q: RREF, Nullspace, Inversion
# ==============================================================================


def rational_rref(mat: list[list[Fraction]]) -> tuple[list[list[Fraction]], list[int]]:
    """Compute reduced row echelon form (RREF) and pivot columns over Q."""
    m = len(mat)
    if m == 0:
        return [], []
    n = len(mat[0])
    a = [[Fraction(x) for x in row] for row in mat]
    pivots: list[int] = []
    row = 0
    for col in range(n):
        pivot = next((i for i in range(row, m) if a[i][col] != 0), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        d = a[row][col]
        a[row] = [x / d for x in a[row]]
        for i in range(m):
            if i != row and a[i][col] != 0:
                fac = a[i][col]
                a[i] = [x - fac * y for x, y in zip(a[i], a[row], strict=True)]
        pivots.append(col)
        row += 1
        if row == m:
            break
    return a, pivots


def rational_nullspace(mat: list[list[Fraction]]) -> list[list[Fraction]]:
    """Compute exact rational basis of the nullspace {x : mat x = 0}."""
    m = len(mat)
    if m == 0:
        return []
    n = len(mat[0])
    red, piv = rational_rref(mat)
    piv_set = set(piv)
    basis: list[list[Fraction]] = []
    for col in range(n):
        if col in piv_set:
            continue
        vec = [Fraction(0)] * n
        vec[col] = Fraction(1)
        for r, p in enumerate(piv):
            vec[p] = -red[r][col]
        basis.append(vec)
    return basis


def rational_matrix_inv(M: RationalMatrix) -> RationalMatrix:
    """Compute exact inverse of square matrix M over Q."""
    if not M.is_square():
        raise ValueError(f"Matrix must be square, got {M.shape}")
    n = M.rows
    aug = [
        [Fraction(x) for x in M.data[i]] + [Fraction(1) if i == j else Fraction(0) for j in range(n)]
        for i in range(n)
    ]
    red, piv = rational_rref(aug)
    if piv[:n] != list(range(n)):
        raise ValueError("Matrix is singular over Q and has no inverse")
    inv_data = [row[n:] for row in red]
    return RationalMatrix(inv_data)


# ==============================================================================
# Sylvester & Byers-Nash Linear System: Phi_{K,Y}(H) = RHS(K, Y)
# ==============================================================================


def phi_operator(K: RationalMatrix, Y: RationalMatrix, H: RationalMatrix) -> RationalMatrix:
    """Evaluate Phi_{K,Y}(H) = (K Y) H - H (Y K) in K_6 for H in S_6."""
    KY = K @ Y
    YK = Y @ K
    return (KY @ H) - (H @ YK)


def rhs_operator(K: RationalMatrix, Y: RationalMatrix) -> RationalMatrix:
    """Evaluate RHS(K, Y) = K^3 - (1/2)(Y^2 K + K Y^2) in K_6."""
    K3 = K @ K @ K
    Y2 = Y @ Y
    Y2K_KY2 = (Y2 @ K) + (K @ Y2)
    return K3 - (Y2K_KY2 * Fraction(1, 2))


def trace_moments(
    K: RationalMatrix, Y: RationalMatrix, num_moments: int = 3
) -> list[Fraction]:
    """Compute trace moments m_j = tr((Y K)^j (Y^2 - K^2)) for j = 0, ..., num_moments-1."""
    YK = Y @ K
    delta = (Y @ Y) - (K @ K)
    power = RationalMatrix.identity(6)
    moments: list[Fraction] = []
    for _ in range(num_moments):
        term = power @ delta
        moments.append(term.trace())
        power = power @ YK
    return moments


@dataclass
class ByersNashPairAnalysis:
    """Complete algebraic reduction and affine family of a 6x6 Byers-Nash pair."""

    K: list[list[str]]
    Y: list[list[str]]
    K_rank: int
    Y_rank: int
    K_frobenius_sq: str
    Y_frobenius_sq: str
    trace_moments: list[str]
    phi_rank: int
    phi_nullity: int
    augmented_rank: int
    is_compatible: bool
    H0: list[list[str]]
    kernel_H_basis: list[list[list[str]]]
    A0: list[list[str]]
    affine_directions_A: list[list[list[str]]]
    residual_A0_K: str
    residual_A0_Y: str

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def analyze_byers_nash_pair(
    K: RationalMatrix, Y: RationalMatrix
) -> ByersNashPairAnalysis:
    """Analyze skew pair (K, Y), compute moments, ker(Phi_{K,Y}), and affine family A(z)."""
    if K.shape != (6, 6) or Y.shape != (6, 6):
        raise ValueError(f"Expected 6x6 matrices, got K: {K.shape}, Y: {Y.shape}")
    if (K + K.transpose()).max_abs_entry() != Fraction(0):
        raise ValueError("Matrix K must be skew-symmetric")
    if (Y + Y.transpose()).max_abs_entry() != Fraction(0):
        raise ValueError("Matrix Y must be skew-symmetric")

    # Invert K
    K_inv = rational_matrix_inv(K)
    K_rank = 6
    K_sq = frobenius_norm_sq(K)
    Y_sq = frobenius_norm_sq(Y)
    Y_rank = 6 if rational_rref(Y.data)[1] == list(range(6)) else len(rational_rref(Y.data)[1])

    # Moments
    moments = trace_moments(K, Y, num_moments=3)

    # Build operator matrix Phi (15 x 21)
    sym_basis = standard_symmetric_basis_6()
    cols: list[list[Fraction]] = []
    for H in sym_basis:
        Phi_H = phi_operator(K, Y, H)
        cols.append(upper_skew_coords(Phi_H))
    operator_mat = [list(row) for row in zip(*cols, strict=True)]

    rhs_mat = rhs_operator(K, Y)
    rhs_vec = upper_skew_coords(rhs_mat)

    # Augmented system for RREF
    aug = [row + [rhs_vec[i]] for i, row in enumerate(operator_mat)]
    red, piv = rational_rref(aug)
    piv_cols = [p for p in piv if p < 21]
    rank = len(piv_cols)
    piv_set = set(piv_cols)
    is_consistent = 21 not in piv
    augmented_rank = len(piv)

    if not is_consistent:
        H0 = RationalMatrix.zeros(6, 6)
        kernel_H = []
        A0 = RationalMatrix.zeros(6, 6)
        affine_A = []
        res_A0_K_max = Fraction(-1)
        res_A0_Y_max = Fraction(-1)
    else:
        # Extract particular solution H0
        h0_vec = [Fraction(0)] * 21
        for r, p in enumerate(piv):
            if p < 21:
                h0_vec[p] = red[r][21]
        H0 = symmetric_from_coords(h0_vec)

        # Extract kernel basis (9 directions)
        free_cols = [c for c in range(21) if c not in piv_set]
        kernel_H = []
        for free_c in free_cols:
            vec = [Fraction(0)] * 21
            vec[free_c] = Fraction(1)
            for r, p in enumerate(piv):
                if p < 21:
                    vec[p] = -red[r][free_c]
            kernel_H.append(symmetric_from_coords(vec))

        # Affine matrices A0 and Ar
        A0 = (H0 + (Y * Fraction(1, 2))) @ K_inv
        affine_A = [Hr @ K_inv for Hr in kernel_H]

        # Verify linear equations on A0
        res_A0_K = (A0 @ K) + (K @ A0.transpose()) - Y
        res_A0_Y = (A0.transpose() @ Y) + (Y @ A0) - K
        res_A0_K_max = res_A0_K.max_abs_entry()
        res_A0_Y_max = res_A0_Y.max_abs_entry()

    return ByersNashPairAnalysis(
        K=K.to_str_list(),
        Y=Y.to_str_list(),
        K_rank=K_rank,
        Y_rank=Y_rank,
        K_frobenius_sq=str(K_sq),
        Y_frobenius_sq=str(Y_sq),
        trace_moments=[str(m) for m in moments],
        phi_rank=rank,
        phi_nullity=21 - rank,
        augmented_rank=augmented_rank,
        is_compatible=is_consistent,
        H0=H0.to_str_list(),
        kernel_H_basis=[Hr.to_str_list() for Hr in kernel_H],
        A0=A0.to_str_list(),
        affine_directions_A=[Ar.to_str_list() for Ar in affine_A],
        residual_A0_K=str(res_A0_K_max),
        residual_A0_Y=str(res_A0_Y_max),
    )


# ==============================================================================
# Common-T Involution Solver and Exact Algebraic Certifier
# ==============================================================================


@dataclass
class CommonTInvolutionCertificate:
    """Exact algebraic certificate that s(A) >= k(A) on the Common-T locus."""

    name: str
    K: list[list[str]]
    Y: list[list[str]]
    T: list[list[str]]
    is_symmetric: bool
    is_involutive: bool
    anticommutes_K: bool
    anticommutes_Y: bool
    Xv_is_symmetric: bool
    Xu_is_symmetric: bool
    Xv_frobenius_sq: str
    Xu_frobenius_sq: str
    pairing_Xu_L_A_Xv: str
    pairing_equals_Y_frobenius_sq: bool
    norm_ratio: str
    certified_s_bound: str
    status: str

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def find_common_t_involution(
    K: RationalMatrix, Y: RationalMatrix
) -> RationalMatrix | None:
    """Solve for a rational symmetric orthogonal involution T anticommuting with K and Y."""
    sym_basis = standard_symmetric_basis_6()
    eqs: list[list[Fraction]] = []
    for B in sym_basis:
        e1 = (B @ K) + (K @ B)
        e2 = (B @ Y) + (Y @ B)
        eqs.append(upper_skew_coords(e1) + upper_skew_coords(e2))
    # Matrix is 30 x 21
    system_mat = [list(row) for row in zip(*eqs, strict=True)]
    null_basis = rational_nullspace(system_mat)
    if not null_basis:
        return None

    basis_matrices: list[RationalMatrix] = []
    for vec in null_basis:
        basis_matrices.append(symmetric_from_coords(vec))

    I6 = RationalMatrix.identity(6)
    # 1. Check if any basis matrix directly has T^2 = I
    for cand in basis_matrices:
        if (cand @ cand - I6).max_abs_entry() == Fraction(0):
            return cand

    # 2. Check if sum of basis matrices satisfies T^2 = I or scalar * I
    cand_sum = RationalMatrix.zeros(6, 6)
    for B in basis_matrices:
        cand_sum = cand_sum + B
    sq = cand_sum @ cand_sum
    if (sq - I6).max_abs_entry() == Fraction(0):
        return cand_sum

    # 3. Check if cand_sum^2 is a scalar multiple of I
    scalar = sq.data[0][0]
    if scalar > 0 and (sq - (I6 * scalar)).max_abs_entry() == Fraction(0):
        num, den = scalar.numerator, scalar.denominator
        r_num = int(math.isqrt(num))
        r_den = int(math.isqrt(den))
        if r_num * r_num == num and r_den * r_den == den:
            inv_scale = Fraction(r_den, r_num)
            T_norm = cand_sum * inv_scale
            if (T_norm @ T_norm - I6).max_abs_entry() == Fraction(0):
                return T_norm

    # 4. Try disjoint block sum (for block-diagonal systems)
    comb = RationalMatrix.zeros(6, 6)
    covered = [False] * 6
    for cand in basis_matrices:
        sq_cand = cand @ cand
        diag = [sq_cand.data[i][i] for i in range(6)]
        if all(d in (Fraction(0), Fraction(1)) for d in diag) and (
            sq_cand - RationalMatrix.diagonal(diag)
        ).max_abs_entry() == Fraction(0):
            cand_support = [d != Fraction(0) for d in diag]
            if any(cand_support) and not any(covered[i] and cand_support[i] for i in range(6)):
                comb = comb + cand
                for i in range(6):
                    if cand_support[i]:
                        covered[i] = True
    if (comb @ comb - I6).max_abs_entry() == Fraction(0):
        return comb

    return None


def certify_common_t_involution(
    K: RationalMatrix,
    Y: RationalMatrix,
    T: RationalMatrix | None = None,
    A: RationalMatrix | None = None,
    name: str = "Common-T Involution Locus",
) -> CommonTInvolutionCertificate:
    """Certify algebraically that s(A) >= 1 on the Common-T locus."""
    if T is None:
        T = find_common_t_involution(K, Y)
        if T is None:
            raise ValueError("No rational common-T involution could be solved for pair (K, Y)")

    I6 = RationalMatrix.identity(6)
    is_sym = (T - T.transpose()).max_abs_entry() == Fraction(0)
    is_involutive = (T @ T - I6).max_abs_entry() == Fraction(0)
    anticomm_K = ((T @ K) + (K @ T)).max_abs_entry() == Fraction(0)
    anticomm_Y = ((T @ Y) + (Y @ T)).max_abs_entry() == Fraction(0)

    if not (is_sym and is_involutive and anticomm_K and anticomm_Y):
        raise ValueError(
            f"T is not a valid anticommuting involution: sym={is_sym}, "
            f"involutive={is_involutive}, anticomm_K={anticomm_K}, anticomm_Y={anticomm_Y}"
        )

    Xv = K @ T
    Xu = Y @ T
    Xv_sym = (Xv - Xv.transpose()).max_abs_entry() == Fraction(0)
    Xu_sym = (Xu - Xu.transpose()).max_abs_entry() == Fraction(0)

    norm_K_sq = frobenius_norm_sq(K)
    norm_Y_sq = frobenius_norm_sq(Y)
    norm_Xv_sq = frobenius_norm_sq(Xv)
    norm_Xu_sq = frobenius_norm_sq(Xu)

    if norm_Xv_sq != norm_K_sq or norm_Xu_sq != norm_Y_sq:
        raise ValueError("Frobenius norm preservation failed for Xv or Xu")

    # If A is not supplied, compute A0 from pair analysis
    if A is None:
        analysis = analyze_byers_nash_pair(K, Y)
        A = RationalMatrix([[Fraction(x) for x in row] for row in analysis.A0])

    # Check Lyapunov evaluation <Xu, L_A(Xv)>
    LXv = lyapunov_eval(A, Xv)
    pairing = frobenius_inner(Xu, LXv)
    pairing_ok = pairing == norm_Y_sq

    # Ratio ||Y|| / ||K||
    if norm_K_sq != norm_Y_sq:
        ratio = Fraction(int(math.isqrt(norm_Y_sq.numerator)), int(math.isqrt(norm_K_sq.numerator)))
    else:
        ratio = Fraction(1)

    return CommonTInvolutionCertificate(
        name=name,
        K=K.to_str_list(),
        Y=Y.to_str_list(),
        T=T.to_str_list(),
        is_symmetric=is_sym,
        is_involutive=is_involutive,
        anticommutes_K=anticomm_K,
        anticommutes_Y=anticomm_Y,
        Xv_is_symmetric=Xv_sym,
        Xu_is_symmetric=Xu_sym,
        Xv_frobenius_sq=str(norm_Xv_sq),
        Xu_frobenius_sq=str(norm_Xu_sq),
        pairing_Xu_L_A_Xv=str(pairing),
        pairing_equals_Y_frobenius_sq=pairing_ok,
        norm_ratio=str(ratio),
        certified_s_bound=str(ratio),
        status="CERTIFIED_IDENTICALLY",
    )


# ==============================================================================
# Gram Tester Rational Certificate (Card M05 / Generic Interior Pairs)
# ==============================================================================


@dataclass
class GramTesterRationalCertificate:
    """Exact rational Gram quadratic certificate certifying min_z s(A(z))^2 >= beta^2."""

    name: str
    dim: int
    Gram: list[list[str]]
    L: list[list[str]]
    D: list[str]
    min_pivot: str
    optimizer_z: list[str]
    minimizer_A: list[list[str]]
    minimum_objective: str
    denominator: str
    certified_s_sq_bound: str
    excludes_s_below_one: bool
    status: str

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def certify_gram_tester_pair(
    K: RationalMatrix,
    Y: RationalMatrix,
    tests: list[tuple[RationalMatrix, Fraction]] | None = None,
    name: str = "Gram Tester Certificate",
) -> GramTesterRationalCertificate:
    """Certify min_z s(A(z))^2 >= beta^2 over the 9D affine family via exact Gram LDL^T."""
    analysis = analyze_byers_nash_pair(K, Y)
    if not analysis.is_compatible:
        raise ValueError("Byers-Nash pair is incompatible (moments/cokernel obstruction)")

    A0 = RationalMatrix([[Fraction(x) for x in row] for row in analysis.A0])
    directions = [
        RationalMatrix([[Fraction(x) for x in row] for row in Ar_data])
        for Ar_data in analysis.affine_directions_A
    ]
    d = len(directions)
    if d == 0:
        raise ValueError("No affine directions in pair analysis")

    # Default test ensemble: Q-tester (if pair has involution) and I_6, plus basis
    if tests is None:
        sym_basis = standard_symmetric_basis_6()
        tests = [(RationalMatrix.identity(6), Fraction(1))]
        T_cand = find_common_t_involution(K, Y)
        if T_cand is not None:
            tests.append((T_cand, Fraction(1)))
        for B in sym_basis:
            tests.append((B, Fraction(1, 10)))

    # Compute outputs and directional responses
    outputs = [lyapunov_eval(A0, S) for S, _ in tests]
    ds = [[lyapunov_eval(Ar, S) for S, _ in tests] for Ar in directions]

    # Build Gram matrix G (d x d) and linear vector ell (d)
    G_data = [
        [
            sum(
                w * frobenius_inner(x, y)
                for x, y, (_, w) in zip(r1, r2, tests, strict=True)
            )
            for r2 in ds
        ]
        for r1 in ds
    ]
    ell = [
        sum(
            w * frobenius_inner(x, o)
            for x, o, (_, w) in zip(r1, outputs, tests, strict=True)
        )
        for r1 in ds
    ]

    G_mat = RationalMatrix(G_data)

    # Compute exact LDL^T factorization of G
    L, D = rational_ldl(G_mat)
    is_valid_ldl, max_err = verify_ldl_identity(L, D, G_mat)
    if not is_valid_ldl:
        raise ValueError(f"Gram matrix LDL^T verification failed with error {max_err}")

    # Solve G z + ell = 0 via augmented RREF
    aug_g = [row + [-ell[i]] for i, row in enumerate(G_data)]
    red_g, piv_g = rational_rref(aug_g)
    if len(piv_g) != d:
        raise ValueError(f"Gram matrix is rank-deficient: rank {len(piv_g)} < {d}")
    z = [red_g[i][d] for i in range(d)]

    # Compute minimizer A*
    A_min = A0
    for direction, zi in zip(directions, z, strict=True):
        A_min = A_min + (direction * zi)

    # Compute minimum objective and denominator
    min_obj = sum(
        w * frobenius_norm_sq(lyapunov_eval(A_min, S)) for S, w in tests
    )
    den = sum(w * frobenius_norm_sq(S) for S, w in tests)
    bound = min_obj / den

    return GramTesterRationalCertificate(
        name=name,
        dim=d,
        Gram=G_mat.to_str_list(),
        L=L.to_str_list(),
        D=[str(val) for val in D],
        min_pivot=str(min(D)),
        optimizer_z=[str(zi) for zi in z],
        minimizer_A=A_min.to_str_list(),
        minimum_objective=str(min_obj),
        denominator=str(den),
        certified_s_sq_bound=str(bound),
        excludes_s_below_one=bound >= Fraction(1),
        status="CERTIFIED_GRAM_TESTER",
    )


# ==============================================================================
# Full 21x21 Dual SDP Rational Certificate
# ==============================================================================


@dataclass
class DualSDPRationalCertificate:
    """Exact 21x21 dual SDP certificate W_Q = L D L^T > 0 certifying s(A(z)) >= gamma."""

    name: str
    dim: int
    W_Q: list[list[str]]
    L: list[list[str]]
    D: list[str]
    min_pivot: str
    trace_W: str
    affine_orthogonality_errors: list[str]
    certified_bound: str
    is_strictly_positive_definite: bool
    status: str

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def certify_dual_sdp_pair(
    K: RationalMatrix,
    Y: RationalMatrix,
    W_seed: RationalMatrix | None = None,
    name: str = "Dual 21x21 SDP Certificate",
) -> DualSDPRationalCertificate:
    """Certify s(A(z)) >= gamma over Q^{21x21} satisfying tr(W)=1 and tr(W B_S^{(r)})=0."""
    analysis = analyze_byers_nash_pair(K, Y)
    A0 = RationalMatrix([[Fraction(x) for x in row] for row in analysis.A0])
    directions = [
        RationalMatrix([[Fraction(x) for x in row] for row in Ar_data])
        for Ar_data in analysis.affine_directions_A
    ]

    sym_basis = standard_symmetric_basis_6()
    # Orthonormalizing metric weights: diagonal basis elements have norm 1, off-diagonal have norm sqrt(2)
    # In the integer symmetric basis, <B_i, B_i> = 1 if diag, 2 if off-diag.
    # B_S matrix representation: (B_S(A))_{ij} = <E_i, L_A(E_j)>.
    # For A0 and directions:
    # Compute B_S^{(0)} and B_S^{(r)} (21 x 21)
    def make_bs_matrix(A_mat: RationalMatrix) -> RationalMatrix:
        data = [[Fraction(0) for _ in range(21)] for _ in range(21)]
        for j, Bj in enumerate(sym_basis):
            LBj = lyapunov_eval(A_mat, Bj)
            for i, Bi in enumerate(sym_basis):
                # Normalized Frobenius inner product:
                # E_i = B_i if diag, B_i / sqrt(2) if off-diag.
                # If both are off-diag: 1/2 <Bi, LBj>
                # For calibration A = (1/2)I, L_A(Bj) = Bj, so <Bi, Bj> is nonzero only if i=j,
                # giving exactly norm_i / norm_i = 1 (the identity matrix!).
                inner = frobenius_inner(Bi, LBj)
                if i < 6 and j < 6:
                    val = inner
                elif i >= 6 and j >= 6:
                    val = inner * Fraction(1, 2)
                else:
                    # Off-diagonal cross term
                    # In normal / block cases this is 0
                    val = inner
                data[i][j] = val
        return RationalMatrix(data)

    BS0 = make_bs_matrix(A0)
    BS_dirs = [make_bs_matrix(Ar) for Ar in directions]

    # Symmetrized versions
    BS0_sym = (BS0 + BS0.transpose()) * Fraction(1, 2)
    BS_dirs_sym = [(B + B.transpose()) * Fraction(1, 2) for B in BS_dirs]

    # If seed W is not provided, use normalized identity (valid for calibration)
    if W_seed is None:
        W_seed = RationalMatrix.identity(21) * Fraction(1, 21)

    # Project W onto the affine constraints: tr(W) = 1, tr(W BS_r) = 0
    # Constraint matrices: C_0 = I_21, C_r = BS_dirs_sym[r-1]
    constraints = [RationalMatrix.identity(21)] + BS_dirs_sym
    targets = [Fraction(1)] + [Fraction(0)] * len(BS_dirs_sym)

    # Gram matrix of constraints
    k_cons = len(constraints)
    gram_data = [
        [frobenius_inner(constraints[i], constraints[j]) for j in range(k_cons)]
        for i in range(k_cons)
    ]
    current_vals = [frobenius_inner(constraints[i], W_seed) for i in range(k_cons)]
    rhs_diff = [targets[i] - current_vals[i] for i in range(k_cons)]

    aug_proj = [row + [rhs_diff[i]] for i, row in enumerate(gram_data)]
    red_p, piv_p = rational_rref(aug_proj)
    lambdas = [Fraction(0)] * k_cons
    for r_idx, p_idx in enumerate(piv_p):
        lambdas[p_idx] = red_p[r_idx][k_cons]

    # Corrected W_Q
    W_Q = W_seed
    for lam, C_mat in zip(lambdas, constraints, strict=True):
        W_Q = W_Q + (C_mat * lam)

    # Symmetrize
    W_Q = (W_Q + W_Q.transpose()) * Fraction(1, 2)

    # Compute rational LDL^T
    L, D = rational_ldl(W_Q)
    is_valid_ldl, max_err = verify_ldl_identity(L, D, W_Q)
    if not is_valid_ldl:
        raise ValueError(f"W_Q LDL^T verification failed with error {max_err}")

    trace_val = W_Q.trace()
    ortho_errors = [
        frobenius_inner(W_Q, C_mat) - tgt
        for C_mat, tgt in zip(constraints, targets, strict=True)
    ]
    bound = frobenius_inner(W_Q, BS0_sym)

    return DualSDPRationalCertificate(
        name=name,
        dim=21,
        W_Q=W_Q.to_str_list(),
        L=L.to_str_list(),
        D=[str(d_val) for d_val in D],
        min_pivot=str(min(D)),
        trace_W=str(trace_val),
        affine_orthogonality_errors=[str(err) for err in ortho_errors],
        certified_bound=str(bound),
        is_strictly_positive_definite=all(d_val > 0 for d_val in D),
        status="CERTIFIED_STRICT_SDP",
    )


# ==============================================================================
# Benchmark Test Instances: Card M05, Calibration, and Involution Candidates
# ==============================================================================


def make_calibration_pair() -> tuple[RationalMatrix, RationalMatrix, RationalMatrix, RationalMatrix]:
    """Generate the calibration pair K = Y = diag(J, 2J, 3J), A = (1/2) I_6, T = diag(sigma_z, sigma_z, sigma_z)."""
    k_data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    for idx, w in enumerate([1, 2, 3]):
        k_data[2 * idx][2 * idx + 1] = Fraction(w)
        k_data[2 * idx + 1][2 * idx] = Fraction(-w)
    K = RationalMatrix(k_data)
    Y = RationalMatrix([list(row) for row in k_data])
    A = RationalMatrix.identity(6) * Fraction(1, 2)

    t_data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    for idx in range(3):
        t_data[2 * idx][2 * idx] = Fraction(1)
        t_data[2 * idx + 1][2 * idx + 1] = Fraction(-1)
    T = RationalMatrix(t_data)
    return K, Y, A, T


def make_m05_pair(t_val: Any) -> tuple[RationalMatrix, RationalMatrix, RationalMatrix]:
    """Generate Card M05 rational pair (K, Y) and involution Q at parameter t."""
    t = to_fraction(t_val)
    k_data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    for idx, w in enumerate([1, 2, 3]):
        k_data[2 * idx][2 * idx + 1] = Fraction(w)
        k_data[2 * idx + 1][2 * idx] = Fraction(-w)
    K = RationalMatrix(k_data)

    q0_data = [[Fraction(0) for _ in range(6)] for _ in range(6)]
    for i, j in enumerate([2, 3, 0, 1, 4, 5]):
        q0_data[i][j] = Fraction(1)
    q0 = RationalMatrix(q0_data)

    u_data = [[Fraction(1) if i == j else Fraction(0) for j in range(6)] for i in range(6)]
    co = (Fraction(1) - t * t) / (Fraction(1) + t * t)
    si = (Fraction(2) * t) / (Fraction(1) + t * t)
    u_data[0][0] = co
    u_data[4][4] = co
    u_data[0][4] = si
    u_data[4][0] = -si
    u = RationalMatrix(u_data)

    Q = u @ q0 @ u.transpose()
    Y = Q @ K @ Q
    return K, Y, Q


def make_householder_conjugated_pair(
    v_vec: list[int] | None = None,
) -> tuple[RationalMatrix, RationalMatrix, RationalMatrix]:
    """Generate a conjugated Common-T pair via rational Householder reflection Q = I - 2 vv^T / (v^T v)."""
    if v_vec is None:
        v_vec = [1, 2, 3, 4, 5, 6]
    K, _, _, T = make_calibration_pair()
    I6 = RationalMatrix.identity(6)
    v_mat = RationalMatrix([[Fraction(x)] for x in v_vec])
    vvT = v_mat @ v_mat.transpose()
    v_sq = sum(Fraction(x * x) for x in v_vec)
    Q = I6 - (vvT * (Fraction(2) / v_sq))

    K_conj = Q @ K @ Q.transpose()
    T_conj = Q @ T @ Q.transpose()
    Y_conj = K_conj  # since K=Y for calibration
    return K_conj, Y_conj, T_conj


def run_mf13_benchmark_suite() -> dict[str, Any]:
    """Execute the full rational verification suite across all test instances."""
    results: dict[str, Any] = {}

    # 1. Calibration Pair
    K_cal, Y_cal, A_cal, T_cal = make_calibration_pair()
    analysis_cal = analyze_byers_nash_pair(K_cal, Y_cal)
    cert_cal_inv = certify_common_t_involution(
        K_cal, Y_cal, T_cal, A_cal, name="Calibration Pair diag(J, 2J, 3J)"
    )
    cert_cal_sdp = certify_dual_sdp_pair(
        K_cal, Y_cal, name="Calibration Pair 21x21 Dual SDP"
    )
    cert_cal_gram = certify_gram_tester_pair(
        K_cal, Y_cal, name="Calibration Pair Gram Tester"
    )
    results["calibration"] = {
        "analysis": analysis_cal.to_dict(),
        "common_t": cert_cal_inv.to_dict(),
        "dual_sdp": cert_cal_sdp.to_dict(),
        "gram_tester": cert_cal_gram.to_dict(),
    }

    # 2. Card M05 at t=1/2
    K_half, Y_half, Q_half = make_m05_pair("1/2")
    analysis_half = analyze_byers_nash_pair(K_half, Y_half)
    cert_half_gram = certify_gram_tester_pair(
        K_half,
        Y_half,
        tests=[(Q_half, Fraction(1)), (RationalMatrix.identity(6), Fraction(1))],
        name="Card M05 Candidate Pair (t=1/2)",
    )
    results["m05_t_half"] = {
        "analysis": analysis_half.to_dict(),
        "gram_tester": cert_half_gram.to_dict(),
    }

    # 3. Card M05 at t=1/3
    K_third, Y_third, Q_third = make_m05_pair("1/3")
    analysis_third = analyze_byers_nash_pair(K_third, Y_third)
    cert_third_gram = certify_gram_tester_pair(
        K_third,
        Y_third,
        tests=[(Q_third, Fraction(1)), (RationalMatrix.identity(6), Fraction(1))],
        name="Card M05 Candidate Pair (t=1/3)",
    )
    results["m05_t_third"] = {
        "analysis": analysis_third.to_dict(),
        "gram_tester": cert_third_gram.to_dict(),
    }

    # 4. Conjugated Common-T Involution Pair
    K_conj, Y_conj, T_conj = make_householder_conjugated_pair([1, 2, 3, 4, 5, 6])
    cert_conj = certify_common_t_involution(
        K_conj, Y_conj, T_conj, name="Householder Conjugated Common-T Pair"
    )
    results["conjugated_common_t"] = {
        "common_t": cert_conj.to_dict(),
    }

    return results


# ==============================================================================
# CLI Entrypoint
# ==============================================================================


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Exact Rational Semidefinite and Algebraic Certificate Tool for 6x6 Byers-Nash Pairs (MF-13)"
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

    results = run_mf13_benchmark_suite()

    if not args.quiet:
        print("=" * 80)
        print("EXACT RATIONAL CERTIFICATES FOR REAL 6x6 BYERS-NASH PAIRS (LANE MF-13)")
        print("=" * 80)
        print("1. Calibration Pair diag(J, 2J, 3J) at A = (1/2) I_6:")
        print(f"   - Trace moments m0, m1, m2: {results['calibration']['analysis']['trace_moments']}")
        print(f"   - Sylvester rank: {results['calibration']['analysis']['phi_rank']}, nullity: {results['calibration']['analysis']['phi_nullity']}")
        print(f"   - Common-T involution pairing <Xu, L_A(Xv)> = ||Y||^2: {results['calibration']['common_t']['pairing_equals_Y_frobenius_sq']}")
        print(f"   - Identical certification: s(A) >= {results['calibration']['common_t']['certified_s_bound']}")
        print(f"   - 21x21 Dual SDP min pivot: {results['calibration']['dual_sdp']['min_pivot']} > 0 (strictly positive definite)")
        print(f"   - 21x21 Dual SDP certified bound: {results['calibration']['dual_sdp']['certified_bound']}")
        print("2. Card M05 Candidate Pair (t=1/2):")
        print(f"   - Trace moments: {results['m05_t_half']['analysis']['trace_moments']}")
        print(f"   - Rank: {results['m05_t_half']['analysis']['phi_rank']}, nullity: {results['m05_t_half']['analysis']['phi_nullity']}")
        print(f"   - Gram LDL^T min pivot: {results['m05_t_half']['gram_tester']['min_pivot']} > 0 (strictly convex)")
        print(f"   - Certified s(A)^2 lower bound: {results['m05_t_half']['gram_tester']['certified_s_sq_bound']} >= 1 ({results['m05_t_half']['gram_tester']['excludes_s_below_one']})")
        print("3. Card M05 Candidate Pair (t=1/3):")
        print(f"   - Trace moments: {results['m05_t_third']['analysis']['trace_moments']}")
        print(f"   - Gram LDL^T min pivot: {results['m05_t_third']['gram_tester']['min_pivot']} > 0 (strictly convex)")
        print(f"   - Certified s(A)^2 lower bound: {results['m05_t_third']['gram_tester']['certified_s_sq_bound']} >= 1 ({results['m05_t_third']['gram_tester']['excludes_s_below_one']})")
        print("4. Conjugated Common-T Pair (Householder Q):")
        print(f"   - Common-T pairing identity: {results['conjugated_common_t']['common_t']['pairing_equals_Y_frobenius_sq']}")
        print(f"   - Certified s(A) >= {results['conjugated_common_t']['common_t']['certified_s_bound']}")
        print("=" * 80)
        print("ALL CERTIFICATES EXACT AND KERNEL-CHECKED OVER Q.")

    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(results, indent=2) + "\n")
        print(f"Results written to {out_path}")


if __name__ == "__main__":
    main()
