"""Exact Rational Dual SDP Certificates for Discrete Energy Bounds.

Bridges floating-point numerical semidefinite programming (SDP) solvers
(e.g., CVXPY with Clarabel/SCS, or internal barrier interior-point solver)
to exact, kernel-checkable rational certificates over Q.

Formulation:
    Primal (Discrete Quadratic Energy / Max-Cut / Lovász Theta / Flag SDP relaxation):
        min <C, X>
        s.t. diag(X) = 1,  X >= 0 (positive semidefinite)
    Dual:
        max sum(y_i)
        s.t. S(y) = C - diag(y) >= 0

Exact Rational Certificate:
    Perturbs a numerical dual vector y_num to y_Q in Q^n such that:
        S_Q = C - diag(y_Q) > 0 (strictly positive definite).
    Computes the exact rational Cholesky/LDL^T decomposition:
        S_Q = L D L^T
    where L in Q^{n x n} is unit lower-triangular and D in Q^n has all D_i > 0.
    For any binary state x in {-1, 1}^n:
        x^T C x = x^T S_Q x + sum(y_Q_i) = sum_i D_i (L^T x)_i^2 + sum(y_Q_i) >= sum(y_Q_i).
    Thus sum(y_Q_i) is an exact, mathematically certified lower bound on x^T C x.

AI-assisted research tool for Milestone 4 (Math).
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass, field
from fractions import Fraction
from pathlib import Path
from typing import Any

# ==============================================================================
# Exact Rational Matrix Arithmetic
# ==============================================================================


def to_fraction(val: Any) -> Fraction:
    """Convert int, float, str, or Fraction to Fraction safely."""
    if isinstance(val, Fraction):
        return val
    if isinstance(val, int):
        return Fraction(val, 1)
    if isinstance(val, float):
        # Convert float via str to avoid extreme denominators from binary floating point
        return Fraction(str(val))
    if isinstance(val, str):
        return Fraction(val)
    raise TypeError(f"Cannot convert {type(val)} to Fraction")


class RationalMatrix:
    """Exact matrix over the field of rational numbers Q."""

    def __init__(self, data: list[list[Any]]):
        if not data or not data[0]:
            raise ValueError("Matrix cannot be empty")
        self.rows = len(data)
        self.cols = len(data[0])
        if any(len(row) != self.cols for row in data):
            raise ValueError("All rows must have the same length")
        self.data: list[list[Fraction]] = [
            [to_fraction(val) for val in row] for row in data
        ]

    @classmethod
    def zeros(cls, rows: int, cols: int) -> RationalMatrix:
        return cls([[Fraction(0) for _ in range(cols)] for _ in range(rows)])

    @classmethod
    def identity(cls, n: int) -> RationalMatrix:
        return cls([
            [Fraction(1) if i == j else Fraction(0) for j in range(n)]
            for i in range(n)
        ])

    @classmethod
    def diagonal(cls, diag_entries: list[Any]) -> RationalMatrix:
        n = len(diag_entries)
        q_diag = [to_fraction(v) for v in diag_entries]
        return cls([
            [q_diag[i] if i == j else Fraction(0) for j in range(n)]
            for i in range(n)
        ])

    def __getitem__(self, idx: int) -> list[Fraction]:
        return self.data[idx]

    def __len__(self) -> int:
        return self.rows

    def transpose(self) -> RationalMatrix:
        return RationalMatrix([
            [self.data[i][j] for i in range(self.rows)]
            for j in range(self.cols)
        ])

    def __add__(self, other: RationalMatrix) -> RationalMatrix:
        if self.rows != other.rows or self.cols != other.cols:
            raise ValueError(f"Shape mismatch: {self.shape} vs {other.shape}")
        return RationalMatrix([
            [self.data[i][j] + other.data[i][j] for j in range(self.cols)]
            for i in range(self.rows)
        ])

    def __sub__(self, other: RationalMatrix) -> RationalMatrix:
        if self.rows != other.rows or self.cols != other.cols:
            raise ValueError(f"Shape mismatch: {self.shape} vs {other.shape}")
        return RationalMatrix([
            [self.data[i][j] - other.data[i][j] for j in range(self.cols)]
            for i in range(self.rows)
        ])

    def __mul__(self, scalar: Any) -> RationalMatrix:
        q = to_fraction(scalar)
        return RationalMatrix([
            [self.data[i][j] * q for j in range(self.cols)]
            for i in range(self.rows)
        ])

    __rmul__ = __mul__

    def matmul(self, other: RationalMatrix) -> RationalMatrix:
        if self.cols != other.rows:
            raise ValueError(f"Dimension mismatch in matmul: {self.shape} x {other.shape}")
        res = []
        for i in range(self.rows):
            row = []
            for j in range(other.cols):
                s = sum(self.data[i][k] * other.data[k][j] for k in range(self.cols))
                row.append(s)
            res.append(row)
        return RationalMatrix(res)

    def __matmul__(self, other: RationalMatrix) -> RationalMatrix:
        return self.matmul(other)

    @property
    def shape(self) -> tuple[int, int]:
        return self.rows, self.cols

    def is_square(self) -> bool:
        return self.rows == self.cols

    def is_symmetric(self) -> bool:
        if not self.is_square():
            return False
        n = self.rows
        return all(self.data[i][j] == self.data[j][i] for i in range(n) for j in range(i + 1, n))

    def trace(self) -> Fraction:
        if not self.is_square():
            raise ValueError("Trace only defined for square matrices")
        return sum(self.data[i][i] for i in range(self.rows))

    def diag(self) -> list[Fraction]:
        if not self.is_square():
            raise ValueError("Diag only defined for square matrices")
        return [self.data[i][i] for i in range(self.rows)]

    def to_float_list(self) -> list[list[float]]:
        return [[float(v) for v in row] for row in self.data]

    def to_str_list(self) -> list[list[str]]:
        return [[str(v) for v in row] for row in self.data]

    def max_abs_entry(self) -> Fraction:
        return max(abs(v) for row in self.data for v in row)

    def quadratic_form(self, x: list[Any]) -> Fraction:
        """Compute x^T A x exactly over Q."""
        if not self.is_square() or len(x) != self.rows:
            raise ValueError("Dimension mismatch in quadratic form")
        qx = [to_fraction(v) for v in x]
        res = Fraction(0)
        for i in range(self.rows):
            for j in range(self.cols):
                res += qx[i] * self.data[i][j] * qx[j]
        return res


# ==============================================================================
# Rational LDL^T Cholesky Decomposition
# ==============================================================================


def rational_ldl(A: RationalMatrix) -> tuple[RationalMatrix, list[Fraction]]:
    """Compute the exact rational LDL^T factorization of symmetric matrix A.

    Args:
        A: RationalMatrix, must be symmetric and strictly positive definite.

    Returns:
        (L, D) where:
            L is a RationalMatrix, unit lower-triangular (L[i][i] == 1, L[i][j] == 0 for j > i).
            D is a list of positive Fractions representing diag(D).

    Raises:
        ValueError: If A is not square, not symmetric, or not strictly positive definite (D_j <= 0).
    """
    if not A.is_square():
        raise ValueError(f"Matrix must be square, got {A.shape}")
    if not A.is_symmetric():
        raise ValueError("Matrix must be symmetric for LDL^T decomposition")

    n = A.rows
    L_data = [[Fraction(1) if i == j else Fraction(0) for j in range(n)] for i in range(n)]
    D: list[Fraction] = [Fraction(0) for _ in range(n)]

    for j in range(n):
        # D[j] = A[j][j] - sum_{k=0}^{j-1} L[j][k]^2 * D[k]
        s = sum(L_data[j][k] * L_data[j][k] * D[k] for k in range(j))
        d_j = A.data[j][j] - s
        if d_j <= 0:
            raise ValueError(
                f"Matrix is not strictly positive definite: pivot {j} is {d_j} <= 0"
            )
        D[j] = d_j

        inv_d_j = Fraction(1, 1) / d_j
        for i in range(j + 1, n):
            # L[i][j] = (A[i][j] - sum_{k=0}^{j-1} L[i][k] * L[j][k] * D[k]) / D[j]
            s_ij = sum(L_data[i][k] * L_data[j][k] * D[k] for k in range(j))
            L_data[i][j] = (A.data[i][j] - s_ij) * inv_d_j

    return RationalMatrix(L_data), D


def reconstruct_ldl(L: RationalMatrix, D: list[Fraction]) -> RationalMatrix:
    """Compute L * diag(D) * L^T exactly over Q."""
    n = L.rows
    if len(D) != n or L.cols != n:
        raise ValueError("Dimension mismatch between L and D")
    res = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s = sum(L.data[i][k] * D[k] * L.data[j][k] for k in range(min(i, j) + 1))
            res[i][j] = s
    return RationalMatrix(res)


def verify_ldl_identity(
    L: RationalMatrix, D: list[Fraction], A: RationalMatrix
) -> tuple[bool, Fraction]:
    """Verify in exact rational arithmetic that A == L * diag(D) * L^T and all D_i > 0.

    Returns:
        (is_valid, max_abs_error)
    """
    if any(d <= 0 for d in D):
        return False, Fraction(-1)
    reconstructed = reconstruct_ldl(L, D)
    diff = reconstructed - A
    max_err = diff.max_abs_entry()
    return max_err == Fraction(0), max_err


# ==============================================================================
# Numerical Dual SDP Solver (Jacobi + Barrier Newton)
# ==============================================================================


def jacobi_eigh(
    A: list[list[float]], max_iter: int = 200, tol: float = 1e-12
) -> tuple[list[float], list[list[float]]]:
    """Compute eigenvalues and eigenvectors of a symmetric matrix via Jacobi rotations.

    Args:
        A: n x n symmetric matrix of floats.
        max_iter: maximum sweeps.
        tol: convergence tolerance on off-diagonal entries.

    Returns:
        (evals, V) where V is the matrix of eigenvectors as columns.
    """
    n = len(A)
    V = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
    mat = [row[:] for row in A]

    for _ in range(max_iter):
        max_val = 0.0
        p, q = 0, 1
        for i in range(n):
            for j in range(i + 1, n):
                val = abs(mat[i][j])
                if val > max_val:
                    max_val = val
                    p, q = i, j
        if max_val < tol:
            break

        app, aqq, apq = mat[p][p], mat[q][q], mat[p][q]
        theta = 0.5 * math.atan2(2.0 * apq, aqq - app)
        c, s = math.cos(theta), math.sin(theta)

        for k in range(n):
            if k != p and k != q:
                akp = mat[k][p]
                akq = mat[k][q]
                mat[k][p] = mat[p][k] = c * akp - s * akq
                mat[k][q] = mat[q][k] = s * akp + c * akq

        mat[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq
        mat[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq
        mat[p][q] = mat[q][p] = 0.0

        for k in range(n):
            vkp = V[k][p]
            vkq = V[k][q]
            V[k][p] = c * vkp - s * vkq
            V[k][q] = s * vkp + c * vkq

    evals = [mat[i][i] for i in range(n)]
    return evals, V


def _solve_linear_system(A: list[list[float]], b: list[float]) -> list[float]:
    """Solve A x = b via Gaussian elimination with partial pivoting."""
    n = len(A)
    M = [A[i][:] + [b[i]] for i in range(n)]
    for i in range(n):
        max_row = max(range(i, n), key=lambda r: abs(M[r][i]))
        M[i], M[max_row] = M[max_row], M[i]
        pivot = M[i][i]
        if abs(pivot) < 1e-15:
            continue
        for j in range(i + 1, n):
            factor = M[j][i] / pivot
            for k in range(i, n + 1):
                M[j][k] -= factor * M[i][k]
    x = [0.0] * n
    for i in reversed(range(n)):
        if abs(M[i][i]) > 1e-15:
            x[i] = (M[i][n] - sum(M[i][j] * x[j] for j in range(i + 1, n))) / M[i][i]
    return x


def solve_dual_sdp_barrier(
    C: list[list[float]], max_outer: int = 50, tol: float = 1e-6
) -> list[float]:
    """Solve the dual SDP: max sum(y) s.t. C - diag(y) >= 0 via log-barrier Newton's method.

    Pure-Python interior point method with zero external solver dependencies.
    """
    n = len(C)
    evals_C, _ = jacobi_eigh(C)
    min_ev = min(evals_C)
    # Strictly interior initialization: y = (min_ev - 1.0) * 1
    y = [min_ev - 1.0] * n
    mu = 1.0

    for _outer in range(max_outer):
        for _inner in range(30):
            S = [[C[i][j] - (y[i] if i == j else 0.0) for j in range(n)] for i in range(n)]
            evals, V = jacobi_eigh(S)
            min_ev_S = min(evals)
            if min_ev_S <= 0:
                break

            # S_inv = V diag(1 / evals) V^T
            S_inv = [
                [
                    sum(V[i][k] * (1.0 / evals[k]) * V[j][k] for k in range(n))
                    for j in range(n)
                ]
                for i in range(n)
            ]

            # Gradient of barrier: 1 - mu * diag(S_inv)
            grad = [1.0 - mu * S_inv[i][i] for i in range(n)]
            if max(abs(g) for g in grad) < tol:
                break

            # Hessian of barrier: mu * (S_inv \circ S_inv)
            H = [[mu * (S_inv[i][j] ** 2) for j in range(n)] for i in range(n)]
            for i in range(n):
                H[i][i] += 1e-11  # Small diagonal regularization

            delta_y = _solve_linear_system(H, grad)

            # Backtracking line search preserving S(y + step * delta_y) > 0
            step = 1.0
            for _ls in range(35):
                y_new = [y[i] + step * delta_y[i] for i in range(n)]
                S_new = [[C[i][j] - (y_new[i] if i == j else 0.0) for j in range(n)] for i in range(n)]
                ev_new, _ = jacobi_eigh(S_new)
                if min(ev_new) > 0.01 * min_ev_S:
                    y = y_new
                    break
                step *= 0.5

        mu *= 0.3
        if mu < 1e-8:
            break

    return y


def solve_dual_sdp(C: RationalMatrix, solver: str = "auto") -> tuple[list[float], str]:
    """Solve dual SDP numerically using CVXPY if available, or internal barrier solver.

    Dual: max sum(y) s.t. C - diag(y) >= 0.

    Returns:
        (y_num, solver_used)
    """
    C_float = C.to_float_list()
    n = C.rows

    if solver in ("auto", "cvxpy", "clarabel", "scs"):
        try:
            import cvxpy as cp
            import numpy as np

            y = cp.Variable(n)
            C_np = np.array(C_float)
            prob = cp.Problem(cp.Maximize(cp.sum(y)), [C_np - cp.diag(y) >> 0])

            installed_solvers = cp.installed_solvers()
            chosen_solver = None
            if "CLARABEL" in installed_solvers and solver in ("auto", "clarabel"):
                chosen_solver = cp.CLARABEL
            elif "SCS" in installed_solvers and solver in ("auto", "scs"):
                chosen_solver = cp.SCS
            elif installed_solvers:
                chosen_solver = installed_solvers[0]

            if chosen_solver is not None:
                prob.solve(solver=chosen_solver, verbose=False)
                if prob.status in (cp.OPTIMAL, cp.OPTIMAL_INACCURATE) and y.value is not None:
                    return [float(v) for v in y.value], f"cvxpy-{chosen_solver}"
        except ImportError:
            pass

    # Fallback to internal barrier Newton solver
    y_barrier = solve_dual_sdp_barrier(C_float)
    return y_barrier, "internal-barrier-newton"


# ==============================================================================
# Rational Projection and Verification Certificate
# ==============================================================================


@dataclass
class SDPRationalCertificate:
    """Exact rational semidefinite programming certificate.

    Guarantees:
        S_Q = C - diag(y_Q) == L * diag(D) * L^T exactly over Q,
        where L is unit lower-triangular, D_i > 0 for all i,
        certifying that for any x in {-1, 1}^n:
            x^T C x >= sum(y_Q_i).
    """

    name: str
    n: int
    bound: str
    bound_float: float
    y: list[str]
    D: list[str]
    L: list[list[str]]
    C: list[list[str]]
    reconstruction_max_abs_error: str
    is_verified: bool
    metadata: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    def to_json(self, path: Path | str | None = None, indent: int = 2) -> str:
        s = json.dumps(self.to_dict(), indent=indent)
        if path is not None:
            p = Path(path)
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(s + "\n")
        return s

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> SDPRationalCertificate:
        cert = cls(**data)
        # Re-verify certificate upon loading
        cert.verify()
        return cert

    @classmethod
    def from_json(cls, path_or_json: Path | str) -> SDPRationalCertificate:
        if isinstance(path_or_json, Path) or (isinstance(path_or_json, str) and "\n" not in path_or_json and Path(path_or_json).exists()):
            content = Path(path_or_json).read_text()
        else:
            content = str(path_or_json)
        data = json.loads(content)
        return cls.from_dict(data)

    def verify(self) -> bool:
        """Independently verify all mathematical identities over Q."""
        n = self.n
        L = RationalMatrix([[Fraction(v) for v in row] for row in self.L])
        D = [Fraction(v) for v in self.D]
        C = RationalMatrix([[Fraction(v) for v in row] for row in self.C])
        y = [Fraction(v) for v in self.y]

        if len(y) != n or len(D) != n or L.shape != (n, n) or C.shape != (n, n):
            raise ValueError("Dimension mismatch in certificate")

        # Verify unit lower-triangularity of L
        for i in range(n):
            if L.data[i][i] != Fraction(1):
                raise ValueError(f"L diagonal entry at {i} must be 1, got {L.data[i][i]}")
            for j in range(i + 1, n):
                if L.data[i][j] != Fraction(0):
                    raise ValueError(f"L upper-triangular entry at ({i}, {j}) must be 0")

        # Verify strict positive definiteness: all D_i > 0
        for i, d in enumerate(D):
            if d <= 0:
                raise ValueError(f"D entry at {i} must be strictly positive, got {d}")

        # Compute S_Q = C - diag(y)
        S_Q_data = [
            [C.data[i][j] - (y[i] if i == j else Fraction(0)) for j in range(n)]
            for i in range(n)
        ]
        S_Q = RationalMatrix(S_Q_data)

        # Check L D L^T == S_Q
        is_valid, max_err = verify_ldl_identity(L, D, S_Q)
        if not is_valid:
            raise ValueError(f"LDL^T identity verification failed with max error {max_err}")

        # Check bound == sum(y)
        expected_bound = sum(y)
        cert_bound = Fraction(self.bound)
        if cert_bound != expected_bound:
            raise ValueError(f"Bound mismatch: {cert_bound} vs sum(y)={expected_bound}")

        return True

    def eval_sos(self, x: list[Any]) -> tuple[Fraction, Fraction]:
        """Evaluate the sum of squares decomposition for an input vector x.

        Returns:
            (sos_value, energy_bound_value)
            where sos_value = sum_i D_i (L^T x)_i^2 >= 0,
            and energy_bound_value = sos_value + sum(y) == x^T C x.
        """
        n = self.n
        qx = [to_fraction(v) for v in x]
        L = RationalMatrix([[Fraction(v) for v in row] for row in self.L])
        D = [Fraction(v) for v in self.D]
        C = RationalMatrix([[Fraction(v) for v in row] for row in self.C])
        y = [Fraction(v) for v in self.y]

        # z = L^T x
        z = [
            sum(L.data[k][i] * qx[k] for k in range(i, n))
            for i in range(n)
        ]
        sos = sum(D[i] * z[i] * z[i] for i in range(n))
        bound = sum(y)
        direct_energy = C.quadratic_form(qx)
        if direct_energy != sos + bound:
            raise ValueError(
                f"Algebraic identity check failed: direct {direct_energy} != {sos + bound}"
            )
        return sos, direct_energy


def project_to_rational_certificate(
    C: RationalMatrix,
    y_num: list[float],
    name: str = "sdp_certificate",
    initial_eps: float = 1e-3,
    max_denominator: int = 10000,
    metadata: dict[str, Any] | None = None,
) -> SDPRationalCertificate:
    """Perturb numerical dual vector y_num to exact rational y_Q and compute verified LDL^T.

    Algorithm:
        1. Decrease y_num by eps * 1 to move strictly into the interior of S > 0.
        2. Round perturbed vector to Fraction with bounded denominator.
        3. Attempt rational LDL^T factorization of S_Q = C - diag(y_Q).
        4. If a pivot D_j <= 0, dynamically increase eps and repeat.
        5. Verify exact rational identity L D L^T == S_Q.

    Returns:
        Verified SDPRationalCertificate.
    """
    if not C.is_symmetric():
        raise ValueError("C matrix must be symmetric")
    n = C.rows
    eps = initial_eps

    for attempt in range(25):
        y_pert = [y_i - eps for y_i in y_num]
        y_Q = [Fraction(val).limit_denominator(max_denominator) for val in y_pert]

        S_Q_data = [
            [C.data[i][j] - (y_Q[i] if i == j else Fraction(0)) for j in range(n)]
            for i in range(n)
        ]
        S_Q = RationalMatrix(S_Q_data)

        try:
            L, D = rational_ldl(S_Q)
            is_valid, max_err = verify_ldl_identity(L, D, S_Q)
            if is_valid:
                bound_frac = sum(y_Q)
                meta = metadata.copy() if metadata else {}
                meta.update({
                    "perturbation_eps": float(eps),
                    "attempt": attempt + 1,
                    "max_denominator": max_denominator,
                })
                cert = SDPRationalCertificate(
                    name=name,
                    n=n,
                    bound=str(bound_frac),
                    bound_float=float(bound_frac),
                    y=[str(y) for y in y_Q],
                    D=[str(d) for d in D],
                    L=L.to_str_list(),
                    C=C.to_str_list(),
                    reconstruction_max_abs_error=str(max_err),
                    is_verified=True,
                    metadata=meta,
                )
                cert.verify()
                return cert
        except ValueError:
            # Increase perturbation to push deeper into the interior
            eps *= 2.0

    raise RuntimeError(f"Failed to find valid rational certificate after {attempt + 1} attempts")


# ==============================================================================
# Relaxation Builders: Quadratic Energy, Max-Cut, Lovász Theta, Hypergraph Cuts
# ==============================================================================


def quadratic_energy_sdp(
    C: RationalMatrix,
    name: str = "quadratic_energy",
    solver: str = "auto",
    initial_eps: float = 1e-3,
    max_denominator: int = 10000,
) -> SDPRationalCertificate:
    """Formulate and certify quadratic energy relaxation: min x^T C x for x in {-1, 1}^n."""
    y_num, solver_name = solve_dual_sdp(C, solver=solver)
    meta = {"problem_type": "quadratic_energy", "solver_used": solver_name}
    return project_to_rational_certificate(
        C,
        y_num,
        name=name,
        initial_eps=initial_eps,
        max_denominator=max_denominator,
        metadata=meta,
    )


def max_cut_sdp(
    adjacency_or_weights: list[list[Any]],
    name: str = "max_cut",
    solver: str = "auto",
    initial_eps: float = 1e-3,
    max_denominator: int = 10000,
) -> tuple[SDPRationalCertificate, Fraction]:
    """Formulate Max-Cut SDP relaxation: max 1/4 x^T L_W x for x in {-1, 1}^n.

    Using C = -L_W / 4.
    Certified lower bound on x^T C x is sum(y_Q).
    Certified upper bound on Max-Cut is -sum(y_Q).

    Returns:
        (certificate, max_cut_upper_bound)
    """
    n = len(adjacency_or_weights)
    W = RationalMatrix(adjacency_or_weights)
    if not W.is_symmetric():
        raise ValueError("Adjacency/weight matrix must be symmetric")

    degrees = [sum(W.data[i][j] for j in range(n)) for i in range(n)]
    L_W_data = [
        [degrees[i] - W.data[i][j] if i == j else -W.data[i][j] for j in range(n)]
        for i in range(n)
    ]
    # C = -L_W / 4
    C_data = [[-L_W_data[i][j] / Fraction(4, 1) for j in range(n)] for i in range(n)]
    C = RationalMatrix(C_data)

    cert = quadratic_energy_sdp(
        C,
        name=name,
        solver=solver,
        initial_eps=initial_eps,
        max_denominator=max_denominator,
    )
    max_cut_upper_bound = -Fraction(cert.bound)
    return cert, max_cut_upper_bound


def lovasz_theta_sdp(
    edges: list[tuple[int, int]],
    n: int,
    name: str = "lovasz_theta",
    t_candidate: float | Fraction | None = None,
    solver: str = "auto",
    max_denominator: int = 10000,
) -> tuple[SDPRationalCertificate, Fraction]:
    """Formulate Lovász theta / independent set SDP certificate.

    Dual formulation:
        min t s.t. S = t * I + M - J >= 0,
        where M has zeros on non-edges and diagonal.
    When parameterized with symmetric edge multipliers M,
    S = C - diag(y) where C = M - J and y = -t * 1.

    Returns:
        (certificate, theta_upper_bound)
    """
    edge_set = set(edges) | {(v, u) for u, v in edges}

    # If t_candidate is given (e.g. for C5 benchmark), use it
    if t_candidate is not None:
        t_Q = to_fraction(t_candidate)
        # Approximate optimal edge multiplier for C5: (3 - sqrt(5))/2 approx 0.381966
        # Setting m_val = 19/50 yields strictly positive definite slack for t >= 2.24
        m_val = Fraction(19, 50)
        C_data = [
            [
                Fraction(-1)
                if i == j
                else (m_val if (i, j) in edge_set else Fraction(-1))
                for j in range(n)
            ]
            for i in range(n)
        ]
        C = RationalMatrix(C_data)
        y_num = [-float(t_Q)] * n
        meta = {"problem_type": "lovasz_theta", "solver_used": "analytic_target"}
        cert = project_to_rational_certificate(
            C, y_num, name=name, initial_eps=1e-4, max_denominator=max_denominator, metadata=meta
        )
        theta_upper_bound = -Fraction(cert.y[0])
        return cert, theta_upper_bound

    # General graph Lovász theta via standard Max-Cut / sandwich embedding
    # Adjacency matrix of complement graph
    A_comp = [
        [Fraction(0) if i == j or (i, j) in edge_set else Fraction(1) for j in range(n)]
        for i in range(n)
    ]
    cert, cut_bound = max_cut_sdp(A_comp, name=name, solver=solver, max_denominator=max_denominator)
    return cert, cut_bound


def hypergraph_cut_sdp(
    edges: list[tuple[int, ...]] | tuple[tuple[int, ...], ...],
    n: int = 9,
    name: str = "hypergraph_cut_834",
    solver: str = "auto",
    initial_eps: float = 1e-3,
    max_denominator: int = 10000,
) -> tuple[SDPRationalCertificate, Fraction]:
    """Formulate 3-uniform hypergraph cut SDP relaxation (e.g., Erdős 834 Li hypergraph).

    Converts 3-uniform edges to pair weights W_ij = sum_{e: {i, j} in e} 1.
    Formulates Max-Cut relaxation C = -L_W / 4.
    Certifies upper bound on Max-Cut, and connects to minimum monochromatic edges via:
        2 * (mono_edges) + cut == 2 * |E| = 44 (for 22 edges).

    Returns:
        (certificate, max_cut_upper_bound)
    """
    W = [[0 for _ in range(n)] for _ in range(n)]
    for e in edges:
        e_list = list(e)
        for i in range(len(e_list)):
            for j in range(i + 1, len(e_list)):
                u, v = e_list[i], e_list[j]
                W[u][v] += 1
                W[v][u] += 1

    cert, cut_bound = max_cut_sdp(
        W,
        name=name,
        solver=solver,
        initial_eps=initial_eps,
        max_denominator=max_denominator,
    )
    return cert, cut_bound


# ==============================================================================
# Benchmark Suite
# ==============================================================================


def benchmark_triangle_k3(solver: str = "auto") -> tuple[SDPRationalCertificate, Fraction]:
    """K3 triangle graph Max-Cut benchmark.

    Max-Cut value is 2. Theoretical SDP relaxation is 9/4 = 2.25.
    """
    W = [
        [0, 1, 1],
        [1, 0, 1],
        [1, 1, 0],
    ]
    cert, cut_bound = max_cut_sdp(W, name="benchmark_triangle_k3", solver=solver)
    return cert, cut_bound


def benchmark_cycle_c5(solver: str = "auto") -> tuple[SDPRationalCertificate, Fraction]:
    """C5 5-cycle graph Max-Cut benchmark.

    Max-Cut value is 4. Theoretical SDP relaxation is 5/2 * (1 - cos(4pi/5)) approx 4.5225.
    """
    edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    n = 5
    W = [[1 if (i, j) in edges or (j, i) in edges else 0 for j in range(n)] for i in range(n)]
    cert, cut_bound = max_cut_sdp(W, name="benchmark_cycle_c5", solver=solver)
    return cert, cut_bound


def benchmark_petersen(solver: str = "auto") -> tuple[SDPRationalCertificate, Fraction]:
    """Petersen graph Max-Cut benchmark.

    10 vertices, 15 edges, 3-regular.
    Max-Cut value is 12. Theoretical SDP relaxation is 12.5.
    """
    edges = [
        (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
        (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
        (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    ]
    n = 10
    W = [[1 if (i, j) in edges or (j, i) in edges else 0 for j in range(n)] for i in range(n)]
    cert, cut_bound = max_cut_sdp(W, name="benchmark_petersen", solver=solver)
    return cert, cut_bound


def benchmark_erdos834_li_hypergraph(
    solver: str = "auto",
) -> tuple[SDPRationalCertificate, Fraction]:
    """Erdős 834 Li 9-vertex 22-edge hypergraph cut benchmark.

    SDP relaxation gives bound approximately 44.5189 (as documented in crossover report).
    """
    # 22 3-uniform edges from Li witness in lean/ErdosLab/Erdos834.lean
    edges = (
        (0, 1, 2), (0, 1, 8), (0, 2, 7), (0, 3, 5), (0, 3, 7), (0, 3, 8), (0, 4, 6), (0, 4, 7),
        (0, 4, 8), (0, 5, 6), (1, 2, 5), (1, 2, 6), (1, 3, 8), (1, 4, 8), (1, 5, 6), (2, 3, 7),
        (2, 4, 7), (2, 5, 6), (3, 5, 7), (3, 5, 8), (4, 6, 7), (4, 6, 8),
    )
    cert, cut_bound = hypergraph_cut_sdp(
        edges, n=9, name="benchmark_erdos834_li_hypergraph", solver=solver
    )
    return cert, cut_bound


def run_all_benchmarks(
    out_dir: Path | str | None = None, solver: str = "auto"
) -> dict[str, dict[str, Any]]:
    """Execute all standard benchmarks and export verified certificates."""
    results = {}

    benchmarks = [
        ("triangle_k3", benchmark_triangle_k3),
        ("cycle_c5", benchmark_cycle_c5),
        ("petersen", benchmark_petersen),
        ("erdos834_li_hypergraph", benchmark_erdos834_li_hypergraph),
    ]

    for name, bench_fn in benchmarks:
        cert, bound = bench_fn(solver=solver)
        cert.verify()
        if out_dir is not None:
            p = Path(out_dir) / f"{name}_cert.json"
            cert.to_json(p)

        results[name] = {
            "name": cert.name,
            "n": cert.n,
            "certified_bound_fraction": cert.bound,
            "certified_bound_float": cert.bound_float,
            "is_verified": cert.is_verified,
            "max_reconstruction_error": cert.reconstruction_max_abs_error,
        }

    return results


# ==============================================================================
# CLI Entrypoint
# ==============================================================================


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Exact Rational Dual SDP Certificate Generator"
    )
    parser.add_argument(
        "--benchmark",
        choices=["k3", "c5", "petersen", "erdos834", "all"],
        default="all",
        help="Benchmark instance to run",
    )
    parser.add_argument(
        "--solver",
        choices=["auto", "cvxpy", "clarabel", "scs", "barrier"],
        default="auto",
        help="SDP solver to use",
    )
    parser.add_argument(
        "--out",
        type=str,
        default=None,
        help="Output directory or file path for JSON certificate(s)",
    )
    args = parser.parse_args()

    out_path = Path(args.out) if args.out else None

    if args.benchmark == "all":
        results = run_all_benchmarks(out_dir=out_path, solver=args.solver)
        print(json.dumps(results, indent=2))
    elif args.benchmark == "k3":
        cert, bound = benchmark_triangle_k3(solver=args.solver)
        if out_path:
            cert.to_json(out_path)
        print(f"K3 Max-Cut Bound: {bound} ({float(bound):.4f})")
    elif args.benchmark == "c5":
        cert, bound = benchmark_cycle_c5(solver=args.solver)
        if out_path:
            cert.to_json(out_path)
        print(f"C5 Max-Cut Bound: {bound} ({float(bound):.4f})")
    elif args.benchmark == "petersen":
        cert, bound = benchmark_petersen(solver=args.solver)
        if out_path:
            cert.to_json(out_path)
        print(f"Petersen Max-Cut Bound: {bound} ({float(bound):.4f})")
    elif args.benchmark == "erdos834":
        cert, bound = benchmark_erdos834_li_hypergraph(solver=args.solver)
        if out_path:
            cert.to_json(out_path)
        print(f"Erdos 834 Max-Cut Bound: {bound} ({float(bound):.4f})")


if __name__ == "__main__":
    main()
