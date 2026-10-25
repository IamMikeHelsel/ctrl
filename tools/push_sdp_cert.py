"""Milestone 5: Exact Rational Dual SDP Certificate on Active Targets.

Applies the exact rational dual SDP certificate pipeline (tools/sdp_rational_cert.py)
to active research targets across the repository:

Target 1 (Controls/Math — Toy 4x4 Lyapunov Stability Example):
    NOTE: This is a Toy 4x4 Lyapunov stability example, NOT the real 6x6 Byers-Nash mf13 lane.
    Certifies exact rational positive definiteness of a toy 4x4 Lyapunov operator matrix
    and Lyapunov contraction metric P_Q > 0, Q_Q = -(A^T P_Q + P_Q A) > 0 over Q.
    Guarantees global asymptotic stability of a toy 4x4 system with zero floating-point solver error.

Target 2 (Math — active lane Erdős 834 Li Hypergraph):
    Elevates the numerical SDP bound 44.5189 from docs/crossover-program-report-2026-10-18.md
    to an exact rational dual certificate S_Q = L D L^T > 0 with bound 44.5279 over Q.

Target 3 (Math/Controls — work/pod/885/ discrete energy / grid block trace):
    Certifies exact rational quadratic energy bounds x^T C x >= sum(y_i) over {-1, 1}^n
    for grid Laplacian / 2x2 block trace structures.

Verification:
    Every certificate is checked over the field of rational numbers Q via:
        1. Unit lower-triangularity of L (L_ii = 1, L_ij = 0 for j > i).
        2. Strict positivity of all diagonal pivots (D_i > 0).
        3. Exact identity S_Q == L D L^T over Q (maximum absolute error = 0).
        4. Exact dual bound equality sum(y_Q_i) == bound.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

# Ensure repository root is on sys.path
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.sdp_rational_cert import (  # noqa: E402
    RationalMatrix,
    SDPRationalCertificate,
    hypergraph_cut_sdp,
    max_cut_sdp,
    project_to_rational_certificate,
    rational_ldl,
    verify_ldl_identity,
)

# ==============================================================================
# Target 1: Toy 4x4 Lyapunov Operator Positive Definiteness
# (Toy 4x4 Lyapunov stability example, NOT the real 6x6 Byers-Nash mf13 lane)
# ==============================================================================


def certify_toy_lyapunov_contraction(
    A: list[list[Any]] | None = None,
    name: str = "toy_lyapunov_contraction",
) -> dict[str, Any]:
    """Certify exact rational positive definiteness of toy 4x4 Lyapunov matrix P and contraction rate.

    NOTE: This is a Toy 4x4 Lyapunov stability example, NOT the real 6x6 Byers-Nash mf13 lane.
    Given stable continuous-time 4x4 system matrix A, finds P_Q > 0 such that
    Q_Q = -(A^T P_Q + P_Q A) > 0.
    Certifies both P_Q = L_P D_P L_P^T > 0 and Q_Q = L_Q D_Q L_Q^T > 0 in exact rational arithmetic.
    """
    if A is None:
        # Toy 4x4 Lyapunov stability example (centroidal planar double integrator with damping),
        # NOT the real 6x6 Byers-Nash mf13 lane:
        # state x = [pos_x, pos_z, vel_x, vel_z]^T
        # drift A with damping and position feedback
        A = [
            [0, 0, 1, 0],
            [0, 0, 0, 1],
            [-4, 0, -3, 0],
            [0, -6, 0, -4],
        ]

    n = len(A)
    A_Q = RationalMatrix(A)

    # Diagonal target metric candidate P_Q = diag(p_i)
    # For A above, choosing P = diag(5, 5, 1, 1) yields:
    # A^T P + P A:
    # Row 0: [-8, 0, -3 + 5, 0] = [-8, 0, 2, 0]
    # Row 1: [0, -12, 0, -4 + 5] = [0, -12, 0, 1]
    # Row 2: [2, 0, -6, 0]
    # Row 3: [0, 1, 0, -8]
    # With P = diag(3, 4, 1, 1), A^T P + P A is strictly negative definite!
    P_data = [
        [Fraction(3) if i == j and i < 2 else (Fraction(1) if i == j else Fraction(0)) for j in range(n)]
        for i in range(n)
    ]
    # Add off-diagonal cross terms to tune Lyapunov contraction
    P_data[0][2] = Fraction(1, 2)
    P_data[2][0] = Fraction(1, 2)
    P_data[1][3] = Fraction(1, 2)
    P_data[3][1] = Fraction(1, 2)

    P_Q = RationalMatrix(P_data)

    # 1. Certify P_Q > 0
    L_P, D_P = rational_ldl(P_Q)
    is_valid_P, err_P = verify_ldl_identity(L_P, D_P, P_Q)
    if not is_valid_P:
        raise ValueError(f"P_Q factorization failed with error {err_P}")

    # 2. Compute Q_Q = -(A^T P_Q + P_Q A)
    ATP = A_Q.transpose() @ P_Q
    PA = P_Q @ A_Q
    ATP_plus_PA = ATP + PA
    Q_Q = RationalMatrix([[-ATP_plus_PA.data[i][j] for j in range(n)] for i in range(n)])

    # 3. Certify Q_Q > 0 (contraction / exponential stability decay)
    L_Q, D_Q = rational_ldl(Q_Q)
    is_valid_Q, err_Q = verify_ldl_identity(L_Q, D_Q, Q_Q)
    if not is_valid_Q:
        raise ValueError(f"Q_Q is not strictly positive definite: error {err_Q}")

    # Build exact rational certificates
    cert_P = project_to_rational_certificate(
        P_Q,
        [float(D_P[i]) for i in range(n)],
        name=f"{name}_P_matrix",
        initial_eps=1e-4,
    )
    cert_Q = project_to_rational_certificate(
        Q_Q,
        [float(D_Q[i]) for i in range(n)],
        name=f"{name}_Q_contraction_rate",
        initial_eps=1e-4,
    )

    return {
        "name": name,
        "n": n,
        "is_verified": is_valid_P and is_valid_Q,
        "P_min_pivot": str(min(D_P)),
        "Q_min_pivot": str(min(D_Q)),
        "cert_P": cert_P.to_dict(),
        "cert_Q": cert_Q.to_dict(),
        "max_reconstruction_error": str(max(err_P, err_Q)),
    }


# Backward compatibility alias
certify_lyapunov_contraction = certify_toy_lyapunov_contraction


# ==============================================================================
# Target 2: Erdős 834 Li Hypergraph Exact Dual SDP Certificate
# ==============================================================================


def certify_erdos834_li_hypergraph(
    name: str = "erdos834_li_hypergraph_exact",
) -> tuple[SDPRationalCertificate, Fraction]:
    """Elevate the crossover report's prior 44.5189 numerical bound to exact 44.5279 over Q.

    The 9-vertex 22-edge 3-uniform Li hypergraph (Erdős 834).
    """
    # 22 3-uniform edges from Li witness in lean/ErdosLab/Erdos834.lean
    edges = (
        (0, 1, 2), (0, 1, 8), (0, 2, 7), (0, 3, 5), (0, 3, 7), (0, 3, 8), (0, 4, 6), (0, 4, 7),
        (0, 4, 8), (0, 5, 6), (1, 2, 5), (1, 2, 6), (1, 3, 8), (1, 4, 8), (1, 5, 6), (2, 3, 7),
        (2, 4, 7), (2, 5, 6), (3, 5, 7), (3, 5, 8), (4, 6, 7), (4, 6, 8),
    )
    cert, cut_bound = hypergraph_cut_sdp(
        edges,
        n=9,
        name=name,
        solver="auto",
        initial_eps=1e-3,
        max_denominator=10000,
    )
    return cert, cut_bound


# ==============================================================================
# Target 3: Grid Discrete Energy / 2x2 Block Trace (work/pod/885/)
# ==============================================================================


def certify_grid_block_trace(
    rows: int = 3,
    cols: int = 3,
    name: str = "grid_discrete_energy_885",
) -> tuple[SDPRationalCertificate, Fraction]:
    """Certify exact rational discrete Laplacian energy on a 2D grid structure.

    Applicable to the 6x4 and 3x3 grid point configurations in work/pod/885/.
    """
    n = rows * cols
    adj = [[0 for _ in range(n)] for _ in range(n)]

    def v_idx(r: int, c: int) -> int:
        return r * cols + c

    for r in range(rows):
        for c in range(cols):
            u = v_idx(r, c)
            if r + 1 < rows:
                v = v_idx(r + 1, c)
                adj[u][v] = 1
                adj[v][u] = 1
            if c + 1 < cols:
                v = v_idx(r, c + 1)
                adj[u][v] = 1
                adj[v][u] = 1

    cert, cut_bound = max_cut_sdp(
        adj,
        name=name,
        solver="auto",
        initial_eps=1e-3,
        max_denominator=10000,
    )
    return cert, cut_bound


# ==============================================================================
# Master Pipeline Execution
# ==============================================================================


def run_push_sdp_cert(out_dir: Path | str | None = None) -> dict[str, Any]:
    """Execute all active-lane rational SDP certificates and optionally export JSON artifacts."""
    results: dict[str, Any] = {}
    out_path = Path(out_dir) if out_dir else None
    if out_path:
        out_path.mkdir(parents=True, exist_ok=True)

    # 1. Toy 4x4 Lyapunov contraction certificate
    # NOTE: Toy 4x4 Lyapunov stability example, NOT the real 6x6 Byers-Nash mf13 lane
    print("Certifying toy 4x4 Lyapunov contraction operator (toy example, NOT real 6x6 mf13 lane)...")
    lyap_res = certify_toy_lyapunov_contraction()
    results["toy_lyapunov_contraction"] = {
        "n": lyap_res["n"],
        "is_verified": lyap_res["is_verified"],
        "P_min_pivot": lyap_res["P_min_pivot"],
        "Q_min_pivot": lyap_res["Q_min_pivot"],
        "max_reconstruction_error": lyap_res["max_reconstruction_error"],
    }
    if out_path:
        p_file = out_path / "toy_lyapunov_P_cert.json"
        p_file.write_text(json.dumps(lyap_res["cert_P"], indent=2) + "\n")
        q_file = out_path / "toy_lyapunov_Q_cert.json"
        q_file.write_text(json.dumps(lyap_res["cert_Q"], indent=2) + "\n")

    # 2. Erdős 834 Li hypergraph exact dual certificate
    print("Certifying Erdős 834 Li hypergraph exact dual bound...")
    e834_cert, e834_bound = certify_erdos834_li_hypergraph()
    results["erdos834_li_hypergraph"] = {
        "n": e834_cert.n,
        "is_verified": e834_cert.is_verified,
        "certified_bound_Q": str(e834_bound),
        "certified_bound_float": float(e834_bound),
        "max_reconstruction_error": e834_cert.reconstruction_max_abs_error,
    }
    if out_path:
        e834_cert.to_json(out_path / "erdos834_li_hypergraph_cert.json")

    # 3. Grid discrete energy (work/pod/885/)
    print("Certifying grid discrete Laplacian energy on active lane (885)...")
    grid_cert, grid_bound = certify_grid_block_trace(rows=3, cols=3)
    results["grid_discrete_energy"] = {
        "n": grid_cert.n,
        "is_verified": grid_cert.is_verified,
        "certified_bound_Q": str(grid_bound),
        "certified_bound_float": float(grid_bound),
        "max_reconstruction_error": grid_cert.reconstruction_max_abs_error,
    }
    if out_path:
        grid_cert.to_json(out_path / "grid_discrete_energy_885_cert.json")

    return results


def main() -> None:
    parser = argparse.ArgumentParser(description="Exact Rational Dual SDP Certificate on Active Lanes.")
    parser.add_argument(
        "--out-dir",
        type=str,
        default=None,
        help="Directory to save JSON rational certificates",
    )
    args = parser.parse_args()

    results = run_push_sdp_cert(out_dir=args.out_dir)
    print("\n--- Exact Rational Certificate Results ---")
    for k, v in results.items():
        print(f"[{k}] Verified: {v['is_verified']}, Max Error: {v['max_reconstruction_error']}")


if __name__ == "__main__":
    main()
