"""Comprehensive test suite for Exact Rational Dual SDP Certificates.

Tests:
1. Exact rational matrix arithmetic over Q (addition, subtraction, multiplication, trace, quadratic form).
2. Rational LDL^T Cholesky decomposition with unit lower-triangular L and all D_i > 0.
3. Strict positive definiteness preservation and rejection of indefinite/singular matrices.
4. Jacobi eigenvalue solver and barrier interior point method.
5. Numerical-to-rational perturbation and projection guaranteeing strictly positive definite slack.
6. Certificate creation, JSON export/import roundtrip, and tamper rejection.
7. Sum-of-Squares (SOS) algebraic identity verification over discrete hypercube states {-1, 1}^n.
8. Standard benchmark topologies:
   - K3 triangle graph (Max-Cut bound 2.25)
   - C5 5-cycle graph (Max-Cut bound 4.5225)
   - Petersen graph (Max-Cut bound 12.5)
   - Erdős 834 Li hypergraph (Max-Cut bound 44.5189)
   - C5 Lovász theta / Shannon capacity bound (theta <= 2.25).
"""

from __future__ import annotations

import sys
from fractions import Fraction
from itertools import product
from pathlib import Path

# Ensure repository root is on sys.path for running pytest directly
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import pytest  # noqa: E402

from tools.sdp_rational_cert import (  # noqa: E402
    RationalMatrix,
    SDPRationalCertificate,
    benchmark_cycle_c5,
    benchmark_erdos834_li_hypergraph,
    benchmark_petersen,
    benchmark_triangle_k3,
    hypergraph_cut_sdp,
    jacobi_eigh,
    lovasz_theta_sdp,
    max_cut_sdp,
    project_to_rational_certificate,
    quadratic_energy_sdp,
    rational_ldl,
    reconstruct_ldl,
    run_all_benchmarks,
    solve_dual_sdp_barrier,
    verify_ldl_identity,
)

# ==============================================================================
# Rational Matrix Arithmetic Tests
# ==============================================================================


def test_rational_matrix_creation_and_properties():
    # From ints, floats, Fractions, strings
    A = RationalMatrix([
        [1, 2.5, Fraction(3, 4)],
        ["5/2", 0, -1],
    ])
    assert A.shape == (2, 3)
    assert not A.is_square()
    assert not A.is_symmetric()
    assert A.data[0][1] == Fraction(5, 2)
    assert A.data[1][0] == Fraction(5, 2)
    assert A.data[0][2] == Fraction(3, 4)

    I3 = RationalMatrix.identity(3)
    assert I3.is_square()
    assert I3.is_symmetric()
    assert I3.trace() == Fraction(3, 1)
    assert I3.diag() == [Fraction(1), Fraction(1), Fraction(1)]


def test_rational_matrix_operations():
    A = RationalMatrix([[1, 2], [3, 4]])
    B = RationalMatrix([[5, 6], [7, 8]])

    # Addition & Subtraction
    C = A + B
    assert C.data == [[Fraction(6), Fraction(8)], [Fraction(10), Fraction(12)]]
    D = B - A
    assert D.data == [[Fraction(4), Fraction(4)], [Fraction(4), Fraction(4)]]

    # Scalar multiplication
    E = A * 2
    assert E.data == [[Fraction(2), Fraction(4)], [Fraction(6), Fraction(8)]]
    E2 = Fraction(1, 2) * E
    assert E2.data == A.data

    # Matrix multiplication
    prod = A @ B
    expected = [[1 * 5 + 2 * 7, 1 * 6 + 2 * 8], [3 * 5 + 4 * 7, 3 * 6 + 4 * 8]]
    assert prod.data == [[Fraction(x) for x in row] for row in expected]

    # Transpose
    At = A.transpose()
    assert At.data == [[Fraction(1), Fraction(3)], [Fraction(2), Fraction(4)]]

    # Quadratic form
    x = [Fraction(1), Fraction(-1)]
    # x^T A x = 1*(1) + 2*(-1) + 3*(-1) + 4*(1) = 1 - 2 - 3 + 4 = 0
    assert A.quadratic_form(x) == Fraction(0)


def test_rational_matrix_error_handling():
    with pytest.raises(ValueError, match="empty"):
        RationalMatrix([])

    with pytest.raises(ValueError, match="same length"):
        RationalMatrix([[1, 2], [3]])

    A = RationalMatrix([[1, 2]])
    B = RationalMatrix([[1], [2], [3]])
    with pytest.raises(ValueError, match="Dimension mismatch in matmul"):
        A.matmul(B)


# ==============================================================================
# Rational LDL^T Factorization Tests
# ==============================================================================


def test_rational_ldl_identity():
    I3 = RationalMatrix.identity(3)
    L, D = rational_ldl(I3)
    assert L.data == I3.data
    assert D == [Fraction(1), Fraction(1), Fraction(1)]

    is_valid, err = verify_ldl_identity(L, D, I3)
    assert is_valid
    assert err == Fraction(0)


def test_rational_ldl_positive_definite():
    # Symmetric strictly positive definite matrix:
    # A = [[4, 2, -1], [2, 5, 2], [-1, 2, 6]]
    A = RationalMatrix([
        [4, 2, -1],
        [2, 5, 2],
        [-1, 2, 6],
    ])
    L, D = rational_ldl(A)

    # Unit lower-triangular check
    for i in range(3):
        assert L.data[i][i] == Fraction(1)
        for j in range(i + 1, 3):
            assert L.data[i][j] == Fraction(0)

    # All D_i > 0
    assert all(d > 0 for d in D)

    # Exact algebraic reconstruction identity
    reconstructed = reconstruct_ldl(L, D)
    diff = reconstructed - A
    assert diff.max_abs_entry() == Fraction(0)

    is_valid, err = verify_ldl_identity(L, D, A)
    assert is_valid
    assert err == Fraction(0)


def test_rational_ldl_fails_on_indefinite():
    # Matrix with negative eigenvalue: [[1, 2], [2, 1]] (evals -1, 3)
    A = RationalMatrix([[1, 2], [2, 1]])
    with pytest.raises(ValueError, match="not strictly positive definite"):
        rational_ldl(A)


def test_rational_ldl_fails_on_singular_positive_semidefinite():
    # K3 Laplacian is positive semidefinite with one 0 eigenvalue
    L_K3 = RationalMatrix([
        [2, -1, -1],
        [-1, 2, -1],
        [-1, -1, 2],
    ])
    with pytest.raises(ValueError, match="not strictly positive definite"):
        rational_ldl(L_K3)


def test_rational_ldl_fails_on_non_symmetric():
    A = RationalMatrix([[1, 2], [3, 4]])
    with pytest.raises(ValueError, match="symmetric"):
        rational_ldl(A)


# ==============================================================================
# Numerical Solver & Jacobi Algorithm Tests
# ==============================================================================


def test_jacobi_eigenvalues():
    # K3 Laplacian: evals 0, 3, 3
    L_K3 = [
        [2.0, -1.0, -1.0],
        [-1.0, 2.0, -1.0],
        [-1.0, -1.0, 2.0],
    ]
    evals, V = jacobi_eigh(L_K3)
    sorted_ev = sorted(evals)
    assert abs(sorted_ev[0] - 0.0) < 1e-10
    assert abs(sorted_ev[1] - 3.0) < 1e-10
    assert abs(sorted_ev[2] - 3.0) < 1e-10

    # Orthogonality of eigenvectors: V^T V == I
    n = 3
    for i in range(n):
        for j in range(n):
            dot = sum(V[k][i] * V[k][j] for k in range(n))
            expected = 1.0 if i == j else 0.0
            assert abs(dot - expected) < 1e-10


def test_solve_dual_sdp_barrier_convergence():
    # K3 Max-Cut: C = -L/4
    # Dual optimal: y = [-0.75, -0.75, -0.75], sum(y) = -2.25
    C = [
        [-0.5, 0.25, 0.25],
        [0.25, -0.5, 0.25],
        [0.25, 0.25, -0.5],
    ]
    y = solve_dual_sdp_barrier(C)
    assert len(y) == 3
    assert abs(sum(y) - (-2.25)) < 1e-4

    # Verify S = C - diag(y) is approximately PSD
    S = [[C[i][j] - (y[i] if i == j else 0.0) for j in range(3)] for i in range(3)]
    evals, _ = jacobi_eigh(S)
    assert min(evals) >= -1e-6


# ==============================================================================
# Rational Projection and Perturbation Tests
# ==============================================================================


def test_project_to_rational_certificate_preserves_psd():
    C = RationalMatrix([
        [Fraction(-2, 4), Fraction(1, 4), Fraction(1, 4)],
        [Fraction(1, 4), Fraction(-2, 4), Fraction(1, 4)],
        [Fraction(1, 4), Fraction(1, 4), Fraction(-2, 4)],
    ])
    # Numerical boundary dual vector
    y_num = [-0.75, -0.75, -0.75]

    cert = project_to_rational_certificate(
        C, y_num, name="test_k3_cert", initial_eps=1e-3, max_denominator=1000
    )

    assert cert.is_verified
    assert cert.n == 3
    assert cert.reconstruction_max_abs_error == "0"

    # All D entries strictly positive Fraction
    for d_str in cert.D:
        d = Fraction(d_str)
        assert d > 0

    # Lower bound strictly less than or equal to -2.25
    bound = Fraction(cert.bound)
    assert bound < Fraction(-225, 100)


# ==============================================================================
# Certificate JSON Export and Tamper Resistance Tests
# ==============================================================================


def test_certificate_serialization_roundtrip(tmp_path: Path):
    C = RationalMatrix([[2, -1], [-1, 2]])
    cert = quadratic_energy_sdp(C, name="test_2x2")

    # Serialize to JSON string
    json_str = cert.to_json()
    cert_loaded = SDPRationalCertificate.from_json(json_str)

    assert cert_loaded.name == cert.name
    assert cert_loaded.bound == cert.bound
    assert cert_loaded.is_verified

    # Serialize to file
    file_path = tmp_path / "cert.json"
    cert.to_json(file_path)
    cert_from_file = SDPRationalCertificate.from_json(file_path)
    assert cert_from_file.name == cert.name
    assert cert_from_file.bound == cert.bound


def test_certificate_rejects_tampered_L():
    C = RationalMatrix([[2, -1], [-1, 2]])
    cert = quadratic_energy_sdp(C, name="test_tamper_L")

    data = cert.to_dict()
    # Corrupt L[1][0]
    data["L"][1][0] = str(Fraction(data["L"][1][0]) + Fraction(1, 10))

    with pytest.raises(ValueError, match="identity verification failed"):
        SDPRationalCertificate.from_dict(data)


def test_certificate_rejects_non_positive_D():
    C = RationalMatrix([[2, -1], [-1, 2]])
    cert = quadratic_energy_sdp(C, name="test_tamper_D")

    data = cert.to_dict()
    # Set D[0] = -1
    data["D"][0] = "-1"

    with pytest.raises(ValueError, match="strictly positive"):
        SDPRationalCertificate.from_dict(data)


def test_certificate_rejects_tampered_bound():
    C = RationalMatrix([[2, -1], [-1, 2]])
    cert = quadratic_energy_sdp(C, name="test_tamper_bound")

    data = cert.to_dict()
    # Fabricate better bound
    data["bound"] = str(Fraction(data["bound"]) + Fraction(100))

    with pytest.raises(ValueError, match="Bound mismatch"):
        SDPRationalCertificate.from_dict(data)


# ==============================================================================
# Sum-of-Squares (SOS) Evaluation Over Discrete States Tests
# ==============================================================================


def test_sos_evaluation_identity_on_hypercube():
    # Max-Cut on K3
    cert, cut_bound = benchmark_triangle_k3()
    assert cert.is_verified

    # Check for all 2^3 = 8 discrete states x in {-1, 1}^3
    for x in product([-1, 1], repeat=3):
        sos, energy = cert.eval_sos(list(x))
        # Sum of squares must be nonnegative
        assert sos >= 0
        # Energy must satisfy x^T C x = sos + bound >= bound
        assert energy >= Fraction(cert.bound)

        # For K3, Max-Cut is 1/4 * x^T L x = - (x^T C x).
        # Since x^T C x >= sum(y), Cut(x) <= -sum(y).
        cut_x = -energy
        assert cut_x <= cut_bound
        # Actual discrete cut on triangle is at most 2
        assert cut_x <= 2


def test_sos_evaluation_on_c5():
    cert, cut_bound = benchmark_cycle_c5()
    assert cert.is_verified

    # Spot-check discrete configurations on C5
    # Max cut of C5 is 4
    for x in product([-1, 1], repeat=5):
        sos, energy = cert.eval_sos(list(x))
        assert sos >= 0
        assert energy >= Fraction(cert.bound)
        cut_x = -energy
        assert cut_x <= 4
        assert cut_x <= cut_bound


# ==============================================================================
# Benchmark Topologies Tests
# ==============================================================================


def test_benchmark_triangle_k3():
    cert, bound = benchmark_triangle_k3()
    assert cert.is_verified
    assert cert.n == 3

    # Theoretical SDP bound is 2.25
    assert float(bound) <= 2.255
    assert float(bound) >= 2.0


def test_benchmark_cycle_c5():
    cert, bound = benchmark_cycle_c5()
    assert cert.is_verified
    assert cert.n == 5

    # Theoretical SDP bound is 5/2 * (1 - cos(4pi/5)) approx 4.5225
    assert float(bound) <= 4.53
    assert float(bound) >= 4.0


def test_benchmark_petersen():
    cert, bound = benchmark_petersen()
    assert cert.is_verified
    assert cert.n == 10

    # Theoretical SDP bound is 12.5 (discrete max cut is 12)
    assert float(bound) <= 12.52
    assert float(bound) >= 12.0


def test_benchmark_erdos834_li_hypergraph():
    cert, bound = benchmark_erdos834_li_hypergraph()
    assert cert.is_verified
    assert cert.n == 9

    # Matches the exact 44.5189 bound in docs/crossover-program-report-2026-10-18.md
    assert float(bound) <= 44.55
    assert float(bound) >= 44.50

    # Relation to monochromatic edges:
    # 2 * mono + cut == 44 => mono = (44 - cut) / 2
    # Since bound approx 44.528 > 44, certified lower bound on mono is:
    mono_bound = (44 - bound) / 2
    assert float(mono_bound) < 0.0  # Shows why numerical SDP bound alone was insufficient


def test_lovasz_theta_c5_relaxation():
    edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
    cert, theta_bound = lovasz_theta_sdp(edges, n=5, t_candidate=Fraction(9, 4))
    assert cert.is_verified
    assert cert.n == 5

    # Lovasz theta(C5) = sqrt(5) approx 2.236068
    assert float(theta_bound) <= 2.26
    assert float(theta_bound) >= 2.23

    # Independence number alpha(C5) <= floor(theta) = 2
    assert int(float(theta_bound)) == 2


def test_max_cut_sdp_custom_weights():
    # 4-cycle graph C4 with cut = 4
    W = [
        [0, 1, 0, 1],
        [1, 0, 1, 0],
        [0, 1, 0, 1],
        [1, 0, 1, 0],
    ]
    cert, cut_bound = max_cut_sdp(W, name="test_c4")
    assert cert.is_verified
    assert float(cut_bound) <= 4.05
    assert float(cut_bound) >= 4.0


def test_hypergraph_cut_sdp_custom():
    # 3-uniform hypergraph on 4 vertices with 2 edges
    edges = ((0, 1, 2), (1, 2, 3))
    cert, cut_bound = hypergraph_cut_sdp(edges, n=4, name="test_small_hypergraph")
    assert cert.is_verified
    assert cert.n == 4
    assert float(cut_bound) > 0


def test_run_all_benchmarks(tmp_path: Path):
    results = run_all_benchmarks(out_dir=tmp_path)
    assert len(results) == 4
    for name in ("triangle_k3", "cycle_c5", "petersen", "erdos834_li_hypergraph"):
        assert name in results
        assert results[name]["is_verified"]
        assert results[name]["max_reconstruction_error"] == "0"
        # Confirm file was written
        json_file = tmp_path / f"{name}_cert.json"
        assert json_file.exists()
        cert_loaded = SDPRationalCertificate.from_json(json_file)
        assert cert_loaded.is_verified
