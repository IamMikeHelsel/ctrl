"""
Unit tests for Homography Decomposition and Two-View Chirality Filtering.
Tests:
- Pure Python 3D vector and matrix math (Vec3, Mat3).
- 3x3 Jacobi eigenvalue decomposition on symmetric matrices.
- Analytical Faugeras & Lustman SVD homography decomposition yielding 8 solutions.
- Algebraic reconstruction test: all 8 solutions reproduce H up to scale.
- Two-view chirality filtering: eliminates 6 solutions, leaving exactly 2 physical poses.
- Ground-truth preservation: true motion (R, t/d, n) is always recovered in the surviving set.
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

import pytest

# Ensure repository root is on sys.path for running pytest directly
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.verify_homography import (  # noqa: E402
    Mat3,
    Vec3,
    decompose_homography,
    filter_physical_solutions,
    jacobi_eigen_3x3,
    rodrigues,
    satisfies_chirality,
)


def test_vec3_operations():
    """Test basic vector algebra."""
    u = Vec3(1.0, 2.0, 3.0)
    v = Vec3(4.0, 5.0, 6.0)

    # Addition & Subtraction
    assert u + v == Vec3(5.0, 7.0, 9.0)
    assert v - u == Vec3(3.0, 3.0, 3.0)
    assert -u == Vec3(-1.0, -2.0, -3.0)

    # Scalar multiplication & division
    assert u * 2.0 == Vec3(2.0, 4.0, 6.0)
    assert 2.0 * u == Vec3(2.0, 4.0, 6.0)
    assert u / 2.0 == Vec3(0.5, 1.0, 1.5)

    # Dot product
    assert u.dot(v) == pytest.approx(32.0)

    # Cross product
    c = u.cross(v)
    assert c == Vec3(-3.0, 6.0, -3.0)
    assert c.dot(u) == pytest.approx(0.0, abs=1e-12)
    assert c.dot(v) == pytest.approx(0.0, abs=1e-12)

    # Norm & Normalization
    assert Vec3(3.0, 4.0, 0.0).norm() == pytest.approx(5.0)
    un = Vec3(3.0, 4.0, 0.0).normalized()
    assert un.norm() == pytest.approx(1.0)
    assert un.x == pytest.approx(0.6)
    assert un.y == pytest.approx(0.8)

    # Error on zero vector normalization
    with pytest.raises(ValueError):
        Vec3(0.0, 0.0, 0.0).normalized()


def test_mat3_operations():
    """Test 3x3 matrix algebra."""
    I = Mat3.identity()
    v = Vec3(1.0, 2.0, 3.0)
    assert I.dot_vec(v) == v

    # Determinant of Identity
    assert I.det() == pytest.approx(1.0)

    # Matrix multiplication
    M = Mat3(
        Vec3(1.0, 2.0, 3.0),
        Vec3(0.0, 1.0, 4.0),
        Vec3(5.0, 6.0, 0.0),
    )
    assert M.transpose().transpose().r0 == M.r0
    assert M.dot_mat(I).r0 == M.r0

    # Determinant of general matrix
    # det(M) = 1*(0 - 24) - 2*(0 - 20) + 3*(0 - 5) = -24 + 40 - 15 = 1
    assert M.det() == pytest.approx(1.0)

    # Outer product
    u = Vec3(1.0, 2.0, 3.0)
    w = Vec3(4.0, 5.0, 6.0)
    O = Mat3.outer(u, w)
    assert O.dot_vec(Vec3(1.0, 0.0, 0.0)) == Vec3(4.0, 8.0, 12.0)
    assert O.r0 == Vec3(4.0, 5.0, 6.0)
    assert O.r1 == Vec3(8.0, 10.0, 12.0)
    assert O.r2 == Vec3(12.0, 15.0, 18.0)

    # Column access
    assert M.col(0) == Vec3(1.0, 0.0, 5.0)
    with pytest.raises(IndexError):
        M.col(3)


def test_jacobi_eigen_3x3_diagonal():
    """Test eigensolver on diagonal matrix."""
    A = Mat3(
        Vec3(5.0, 0.0, 0.0),
        Vec3(0.0, 2.0, 0.0),
        Vec3(0.0, 0.0, 1.0),
    )
    evals, evecs = jacobi_eigen_3x3(A)
    assert evals[0] == pytest.approx(5.0)
    assert evals[1] == pytest.approx(2.0)
    assert evals[2] == pytest.approx(1.0)


def test_jacobi_eigen_3x3_general_symmetric():
    """Test eigensolver on general symmetric positive definite matrix."""
    # Construct A = B Bᵀ
    B = Mat3(
        Vec3(2.0, -1.0, 0.5),
        Vec3(0.0, 1.5, -0.5),
        Vec3(1.0, 0.5, 2.0),
    )
    A = B.dot_mat(B.transpose())

    evals, evecs = jacobi_eigen_3x3(A)

    # Check eigenvalues are sorted descending
    assert evals[0] >= evals[1] >= evals[2]
    assert evals[2] > 0

    # Check eigenvectors are orthonormal: Vᵀ V = I
    for i in range(3):
        assert evecs[i].norm() == pytest.approx(1.0, abs=1e-10)
        for j in range(i + 1, 3):
            assert evecs[i].dot(evecs[j]) == pytest.approx(0.0, abs=1e-10)

    # Check eigenvalue equation: A v_i = λ_i v_i
    for i in range(3):
        Avi = A.dot_vec(evecs[i])
        lam_vi = evecs[i] * evals[i]
        diff = (Avi - lam_vi).norm()
        assert diff == pytest.approx(0.0, abs=1e-10)


def test_homography_pure_rotation():
    """Test homography decomposition for pure rotation (zero translation)."""
    axis = Vec3(0.5, 0.8, -0.3).normalized()
    angle = 0.35  # ~20 degrees
    R_gt = rodrigues(axis, angle)

    # Pure rotation homography: H = R
    H = R_gt

    solutions = decompose_homography(H)
    assert len(solutions) >= 1
    # Check that H reproduces R_gt
    diff = (solutions[0].R - R_gt).frob_norm()
    assert diff == pytest.approx(0.0, abs=1e-6)


def generate_plane_points(n: Vec3, d: float, count: int = 8) -> list[Vec3]:
    """
    Generate visible test points on the plane π: nᵀ X = d.
    Points are chosen so that z > 0 (in front of camera 1).
    """
    # Find two orthogonal vectors tangent to the plane
    if abs(n.z) > 0.5:
        t1 = Vec3(1.0, 0.0, -n.x / n.z).normalized()
    else:
        t1 = Vec3(0.0, 1.0, -n.y / n.z).normalized()
    t2 = n.cross(t1).normalized()

    # Base point on plane closest to origin: X0 = d * n
    X0 = n * d

    points = []
    # Grid of points around X0
    for dx in [-0.2, 0.0, 0.2]:
        for dy in [-0.2, 0.0, 0.2]:
            pt = X0 + (t1 * dx) + (t2 * dy)
            if pt.z > 0.1:  # strictly in front of camera
                points.append(pt)
            if len(points) >= count:
                break
        if len(points) >= count:
            break
    return points


def run_homography_chirality_pipeline(
    R_gt: Mat3,
    t_gt: Vec3,
    n_gt: Vec3,
    d_gt: float,
):
    """
    End-to-end verification helper:
    1. Build planar homography H = R + t' nᵀ where t' = t / d.
    2. Decompose H into 8 mathematical solutions.
    3. Verify all 8 solutions algebraically reconstruct H up to scale.
    4. Apply two-view chirality constraint on visible plane points.
    5. Verify exactly 2 physical solutions survive (Elimination Theorem).
    6. Verify ground-truth motion (R_gt, t'_gt, n_gt) is among the surviving solutions.
    """
    assert d_gt > 0
    n_gt = n_gt.normalized()
    t_prime_gt = t_gt / d_gt

    # 1. Ground truth homography
    H = R_gt + Mat3.outer(t_prime_gt, n_gt)

    # 2. Decompose into candidate solutions
    solutions = decompose_homography(H)
    assert len(solutions) == 8, f"Expected 8 solutions, got {len(solutions)}"

    # 3. Check algebraic reconstruction for ALL 8 solutions
    for idx, sol in enumerate(solutions):
        assert sol.reproduces(H, tol=1e-5), (
            f"Solution {idx} ({sol.branch}) failed algebraic reconstruction"
        )

    # Find candidate normals n_a and n_b
    n_a = solutions[0].n if solutions[0].n.z > 0 else -solutions[0].n
    n_b = solutions[4].n if solutions[4].n.z > 0 else -solutions[4].n

    # Joint visibility cone of both planes matching Lean Elimination Theorem hypotheses:
    # (h_front_a : 0 < n_a ⬝ X) and (h_front_b : 0 < n_b ⬝ X)
    bisect = (n_a + n_b).normalized()
    test_points = [
        bisect * d_gt,
        (bisect + Vec3(0.02, 0.0, 0.0)).normalized() * d_gt,
        (bisect + Vec3(0.0, 0.02, 0.0)).normalized() * d_gt,
        (bisect + Vec3(-0.02, -0.02, 0.0)).normalized() * d_gt,
    ]

    # 4 & 5. Filter by two-view chirality
    surviving = filter_physical_solutions(solutions, test_points)
    assert len(surviving) == 2, (
        f"Elimination theorem violated: expected exactly 2 surviving solutions, got {len(surviving)}"
    )

    # 6. Verify ground truth is among the 2 surviving solutions
    found_gt = False
    for sol in surviving:
        # Check if this solution matches ground truth
        # Normal matches +n_gt, translation matches +t_prime_gt, rotation matches R_gt
        r_diff = (sol.R - R_gt).frob_norm()
        t_diff = (sol.t_prime - t_prime_gt).norm()
        n_diff = (sol.n - n_gt).norm()

        if r_diff < 1e-4 and t_diff < 1e-4 and n_diff < 1e-4:
            found_gt = True
            break

    assert found_gt, (
        f"Ground-truth pose not found among surviving solutions! Surviving: {surviving}"
    )


def test_homography_pure_translation():
    """Test planar homography with pure translation along X and Y."""
    R_gt = Mat3.identity()
    t_gt = Vec3(0.2, -0.15, 0.05)
    n_gt = Vec3(0.0, 0.0, 1.0)
    d_gt = 2.0
    run_homography_chirality_pipeline(R_gt, t_gt, n_gt, d_gt)


def test_homography_rotation_about_y():
    """Test planar homography with rotation about Y-axis and non-zero translation."""
    axis = Vec3(0.0, 1.0, 0.0)
    angle = 0.25  # ~14 degrees
    R_gt = rodrigues(axis, angle)
    t_gt = Vec3(0.15, 0.1, 0.2)
    n_gt = Vec3(0.1, 0.2, 0.95).normalized()
    d_gt = 1.8
    run_homography_chirality_pipeline(R_gt, t_gt, n_gt, d_gt)


def test_homography_oblique_plane():
    """Test planar homography with general 3D rotation, oblique plane and translation."""
    axis = Vec3(1.0, 2.0, 1.5).normalized()
    angle = 0.3  # ~17 degrees
    R_gt = rodrigues(axis, angle)
    t_gt = Vec3(-0.25, 0.15, 0.1)
    n_gt = Vec3(0.3, -0.2, 0.85).normalized()
    d_gt = 1.5
    run_homography_chirality_pipeline(R_gt, t_gt, n_gt, d_gt)


def test_homography_randomized_diverse_poses():
    """
    Test 12 diverse randomized configurations with varied rotations,
    translations, depths, and plane normals facing the camera.
    """
    rng = random.Random(42)

    for _case_idx in range(12):
        # Random axis and angle in [0.1, 0.5] rad (~6 to 30 deg)
        axis = Vec3(
            rng.uniform(-1.0, 1.0),
            rng.uniform(-1.0, 1.0),
            rng.uniform(-1.0, 1.0),
        ).normalized()
        angle = rng.uniform(0.1, 0.45)
        R_gt = rodrigues(axis, angle)

        # Random translation
        t_gt = Vec3(
            rng.uniform(-0.3, 0.3),
            rng.uniform(-0.3, 0.3),
            rng.uniform(0.05, 0.35),
        )

        # Random normal facing camera (n_z in [0.5, 1.0])
        n_gt = Vec3(
            rng.uniform(-0.4, 0.4),
            rng.uniform(-0.4, 0.4),
            rng.uniform(0.6, 1.0),
        ).normalized()

        # Random depth
        d_gt = rng.uniform(1.2, 3.0)

        run_homography_chirality_pipeline(R_gt, t_gt, n_gt, d_gt)


def test_chirality_rejection_behind_camera():
    """Verify that points behind camera 1 (z <= 0) or camera 2 fail chirality."""
    R = Mat3.identity()
    t_prime = Vec3(0.0, 0.0, 0.0)
    n = Vec3(0.0, 0.0, 1.0)

    # Point with negative depth z < 0
    pt_behind = [Vec3(0.0, 0.0, -1.0)]
    assert not satisfies_chirality(R, t_prime, n, pt_behind)

    # Point on plane facing away (n ⬝ X < 0)
    pt_wrong_normal = [Vec3(0.0, 0.0, 1.0)]
    n_away = Vec3(0.0, 0.0, -1.0)
    assert not satisfies_chirality(R, t_prime, n_away, pt_wrong_normal)
