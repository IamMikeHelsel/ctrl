"""
Homography decomposition verification tool in pure Python (no external dependencies).
Implements:
- Pure Python 3D vector and matrix math (Vec3, Mat3).
- Symmetric 3x3 Jacobi eigenvalue decomposition / SVD.
- Faugeras & Lustman analytical homography decomposition yielding 8 solutions.
- Two-view chirality filtering isolating 2 physical poses.
"""

from __future__ import annotations

import math
from dataclasses import dataclass


@dataclass(frozen=True)
class Vec3:
    x: float
    y: float
    z: float

    def __add__(self, other: Vec3) -> Vec3:
        return Vec3(self.x + other.x, self.y + other.y, self.z + other.z)

    def __sub__(self, other: Vec3) -> Vec3:
        return Vec3(self.x - other.x, self.y - other.y, self.z - other.z)

    def __neg__(self) -> Vec3:
        return Vec3(-self.x, -self.y, -self.z)

    def __mul__(self, c: float) -> Vec3:
        return Vec3(c * self.x, c * self.y, c * self.z)

    def __rmul__(self, c: float) -> Vec3:
        return self.__mul__(c)

    def __truediv__(self, c: float) -> Vec3:
        return Vec3(self.x / c, self.y / c, self.z / c)

    def dot(self, other: Vec3) -> float:
        return self.x * other.x + self.y * other.y + self.z * other.z

    def cross(self, other: Vec3) -> Vec3:
        return Vec3(
            self.y * other.z - self.z * other.y,
            self.z * other.x - self.x * other.z,
            self.x * other.y - self.y * other.x,
        )

    def norm(self) -> float:
        return math.sqrt(self.dot(self))

    def normalized(self) -> Vec3:
        n = self.norm()
        if n < 1e-15:
            raise ValueError("Cannot normalize near-zero vector")
        return self / n

    def to_tuple(self) -> tuple[float, float, float]:
        return (self.x, self.y, self.z)


@dataclass(frozen=True)
class Mat3:
    # Stored as 3 row vectors
    r0: Vec3
    r1: Vec3
    r2: Vec3

    @staticmethod
    def from_rows(r0: Vec3, r1: Vec3, r2: Vec3) -> Mat3:
        return Mat3(r0, r1, r2)

    @staticmethod
    def from_cols(c0: Vec3, c1: Vec3, c2: Vec3) -> Mat3:
        return Mat3(
            Vec3(c0.x, c1.x, c2.x),
            Vec3(c0.y, c1.y, c2.y),
            Vec3(c0.z, c1.z, c2.z),
        )

    @staticmethod
    def identity() -> Mat3:
        return Mat3(
            Vec3(1.0, 0.0, 0.0),
            Vec3(0.0, 1.0, 0.0),
            Vec3(0.0, 0.0, 1.0),
        )

    @staticmethod
    def zeros() -> Mat3:
        return Mat3(
            Vec3(0.0, 0.0, 0.0),
            Vec3(0.0, 0.0, 0.0),
            Vec3(0.0, 0.0, 0.0),
        )

    @staticmethod
    def outer(u: Vec3, v: Vec3) -> Mat3:
        return Mat3(
            Vec3(u.x * v.x, u.x * v.y, u.x * v.z),
            Vec3(u.y * v.x, u.y * v.y, u.y * v.z),
            Vec3(u.z * v.x, u.z * v.y, u.z * v.z),
        )

    def col(self, j: int) -> Vec3:
        if j == 0:
            return Vec3(self.r0.x, self.r1.x, self.r2.x)
        elif j == 1:
            return Vec3(self.r0.y, self.r1.y, self.r2.y)
        elif j == 2:
            return Vec3(self.r0.z, self.r1.z, self.r2.z)
        raise IndexError("Column index out of range")

    def __add__(self, other: Mat3) -> Mat3:
        return Mat3(self.r0 + other.r0, self.r1 + other.r1, self.r2 + other.r2)

    def __sub__(self, other: Mat3) -> Mat3:
        return Mat3(self.r0 - other.r0, self.r1 - other.r1, self.r2 - other.r2)

    def __mul__(self, c: float) -> Mat3:
        return Mat3(self.r0 * c, self.r1 * c, self.r2 * c)

    def __rmul__(self, c: float) -> Mat3:
        return self.__mul__(c)

    def __truediv__(self, c: float) -> Mat3:
        return Mat3(self.r0 / c, self.r1 / c, self.r2 / c)

    def dot_vec(self, v: Vec3) -> Vec3:
        return Vec3(self.r0.dot(v), self.r1.dot(v), self.r2.dot(v))

    def dot_mat(self, other: Mat3) -> Mat3:
        c0 = other.col(0)
        c1 = other.col(1)
        c2 = other.col(2)
        return Mat3.from_cols(self.dot_vec(c0), self.dot_vec(c1), self.dot_vec(c2))

    def transpose(self) -> Mat3:
        return Mat3.from_cols(self.r0, self.r1, self.r2)

    def det(self) -> float:
        c0 = self.col(0)
        c1 = self.col(1)
        c2 = self.col(2)
        return c0.dot(c1.cross(c2))

    def frob_norm(self) -> float:
        return math.sqrt(
            self.r0.dot(self.r0) + self.r1.dot(self.r1) + self.r2.dot(self.r2)
        )


def rodrigues(axis: Vec3, angle: float) -> Mat3:
    """Rotation matrix from axis-angle representation using Rodrigues formula."""
    k = axis.normalized()
    cos_a = math.cos(angle)
    sin_a = math.sin(angle)
    # R = I cos_a + (1 - cos_a) k kᵀ + [k]ₓ sin_a
    K = Mat3(
        Vec3(0.0, -k.z, k.y),
        Vec3(k.z, 0.0, -k.x),
        Vec3(-k.y, k.x, 0.0),
    )
    I = Mat3.identity()
    K2 = K.dot_mat(K)
    return I + (sin_a * K) + ((1.0 - cos_a) * K2)


def jacobi_eigen_3x3(A: Mat3, max_iter: int = 50) -> tuple[list[float], list[Vec3]]:
    """
    Eigenvalue decomposition of a 3x3 symmetric matrix via Jacobi rotations.
    Returns:
        (eigenvalues, eigenvectors) where eigenvalues are sorted descending:
        vals[0] >= vals[1] >= vals[2]
        and vecs[i] are unit eigenvectors.
    """
    # Work on a 3x3 list of floats
    a = [
        [A.r0.x, A.r0.y, A.r0.z],
        [A.r1.x, A.r1.y, A.r1.z],
        [A.r2.x, A.r2.y, A.r2.z],
    ]
    # Symmetrize
    for i in range(3):
        for j in range(i + 1, 3):
            avg = 0.5 * (a[i][j] + a[j][i])
            a[i][j] = avg
            a[j][i] = avg

    # Eigenvector matrix V initially I
    v = [
        [1.0, 0.0, 0.0],
        [0.0, 1.0, 0.0],
        [0.0, 0.0, 1.0],
    ]

    for _ in range(max_iter):
        # Find maximum off-diagonal element
        p, q = 0, 1
        max_val = abs(a[0][1])
        if abs(a[0][2]) > max_val:
            max_val = abs(a[0][2])
            p, q = 0, 2
        if abs(a[1][2]) > max_val:
            max_val = abs(a[1][2])
            p, q = 1, 2

        if max_val < 1e-15:
            break

        # Compute Jacobi rotation angle
        diff = a[q][q] - a[p][p]
        if abs(diff) < 1e-15:
            t = 1.0
        else:
            phi = diff / (2.0 * a[p][q])
            t = 1.0 / (abs(phi) + math.sqrt(phi * phi + 1.0))
            if phi < 0:
                t = -t
        c = 1.0 / math.sqrt(t * t + 1.0)
        s = t * c

        # Apply rotation to A: A' = Jᵀ A J
        # Update a[p][p], a[q][q], a[p][q]
        app = a[p][p]
        aqq = a[q][q]
        apq = a[p][q]
        a[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq
        a[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq
        a[p][q] = 0.0
        a[q][p] = 0.0

        for r in range(3):
            if r != p and r != q:
                arp = a[r][p]
                arq = a[r][q]
                a[r][p] = c * arp - s * arq
                a[p][r] = a[r][p]
                a[r][q] = s * arp + c * arq
                a[q][r] = a[r][q]

        # Update eigenvectors V = V J
        for r in range(3):
            vrp = v[r][p]
            vrq = v[r][q]
            v[r][p] = c * vrp - s * vrq
            v[r][q] = s * vrp + c * vrq

    # Extract eigenvalues and eigenvectors
    evals = [a[0][0], a[1][1], a[2][2]]
    evecs = [
        Vec3(v[0][0], v[1][0], v[2][0]).normalized(),
        Vec3(v[0][1], v[1][1], v[2][1]).normalized(),
        Vec3(v[0][2], v[1][2], v[2][2]).normalized(),
    ]

    # Sort descending
    idx = sorted(range(3), key=lambda i: evals[i], reverse=True)
    sorted_evals = [evals[i] for i in idx]
    sorted_evecs = [evecs[i] for i in idx]

    # Ensure right-handed orthonormal basis
    det_v = sorted_evecs[0].dot(sorted_evecs[1].cross(sorted_evecs[2]))
    if det_v < 0:
        sorted_evecs[2] = -sorted_evecs[2]

    return sorted_evals, sorted_evecs


@dataclass
class HomographySolution:
    R: Mat3
    t_prime: Vec3
    n: Vec3
    branch: str  # e.g. "a1", "a2", "b1", "b2" or sign triple

    def reproduces(self, H: Mat3, tol: float = 1e-6) -> bool:
        """Check if R + t' nᵀ = H (up to scale)."""
        reconstructed = self.R + Mat3.outer(self.t_prime, self.n)
        # Normalize both reconstructed and H to compare
        scale_h = H.frob_norm()
        scale_r = reconstructed.frob_norm()
        if scale_h < 1e-15 or scale_r < 1e-15:
            return False
        diff = (reconstructed / scale_r) - (H / scale_h)
        return diff.frob_norm() < tol


def decompose_homography(H: Mat3) -> list[HomographySolution]:
    """
    Analytical Faugeras & Lustman (1988) SVD-based homography decomposition.
    Returns 8 mathematical solutions (R_i, t'_i, n_i) matching the Lean 4 formalization:
    - 2 geometric branches (Branch a / ground truth vs Branch b / dual)
    - 4 discrete sign combinations (eps2, eps3) per branch:
        1. (+, +): proper rotation, true normal, positive translation
        2. (-, -): proper rotation, reversed normal, negative translation
        3. (+, -): reflection branch R + 2 t' nᵀ, reversed normal
        4. (-, +): reflection branch R + 2 t' nᵀ, true normal
    All 8 solutions algebraically reproduce H = R + t' nᵀ up to scale.
    """
    solutions: list[HomographySolution] = []

    # SVD of H via M = Hᵀ H
    M = H.transpose().dot_mat(H)
    evals, evecs = jacobi_eigen_3x3(M)
    d1, d2, d3 = evals
    if d2 <= 0:
        return solutions
    sigma2 = math.sqrt(d2)

    # Normalize H by sigma2 so that lambda2 = 1
    H_norm = H / sigma2
    lam1 = d1 / d2
    lam3 = d3 / d2
    v1, v2, v3 = evecs

    # Pure rotation case
    if abs(lam1 - lam3) < 1e-8:
        solutions.append(
            HomographySolution(
                R=H_norm,
                t_prime=Vec3(0.0, 0.0, 0.0),
                n=Vec3(0.0, 0.0, 1.0),
                branch="pure_rot",
            )
        )
        return solutions

    denom = math.sqrt(max(0.0, lam1 - lam3))
    if denom < 1e-12:
        return solutions

    s1 = math.sqrt(max(0.0, 1.0 - lam3))
    s3 = math.sqrt(max(0.0, lam1 - 1.0))

    # Two unit vectors in span(v1, v3)
    u1 = (s1 * v1 + s3 * v3) / denom
    u2 = (s1 * v1 - s3 * v3) / denom

    branches = [("a", u1), ("b", u2)]

    for branch_name, u in branches:
        # Base normal w = u x v2
        w = u.cross(v2).normalized()

        # Orthonormal frame W = [u, v2, w]
        W = Mat3.from_cols(u, v2, w)

        # Transformed basis: [H u, H v2, H u x H v2]
        Hu = H_norm.dot_vec(u).normalized()
        Hv2 = H_norm.dot_vec(v2).normalized()
        Hw = Hu.cross(Hv2).normalized()
        HW = Mat3.from_cols(Hu, Hv2, Hw)

        # Base rotation R_base = HW * Wᵀ
        R_base = HW.dot_mat(W.transpose())
        n_base = w
        t_base = H_norm.dot_vec(n_base) - R_base.dot_vec(n_base)

        # 4 sign combinations of (eps2, eps3)
        sign_pairs = [
            (+1.0, +1.0, "pos_pos"),
            (-1.0, -1.0, "neg_neg"),
            (+1.0, -1.0, "pos_neg"),
            (-1.0, +1.0, "neg_pos"),
        ]

        for eps2, eps3, sign_label in sign_pairs:
            n = eps3 * n_base
            t_prime = eps2 * t_base
            if eps2 * eps3 > 0:
                R = R_base
            else:
                # Reflection branch: R_base + 2 t_base n_baseᵀ
                R = R_base + (2.0 * Mat3.outer(t_base, n_base))

            solutions.append(
                HomographySolution(
                    R=R,
                    t_prime=t_prime,
                    n=n,
                    branch=f"{branch_name}_{sign_label}",
                )
            )

    return solutions


def satisfies_chirality(
    R: Mat3,
    t_prime: Vec3,
    n: Vec3,
    test_points: list[Vec3],
) -> bool:
    """
    Two-view chirality constraint matching Lean formalization:
    1. Proper rigid rotation: det(R) > 0 (Sign.mul eps2 eps3 = .pos).
    2. Camera 1 depth & positive plane side: n ⬝ X > 0, X.z > 0.
    3. Camera 2 depth & positive plane side: n ⬝ (R X + (n ⬝ X) • t') > 0, (R X + (n ⬝ X) • t').z > 0.
    """
    # 1. Proper rigid rotation: R ∈ SO(3) (Rᵀ R = I, det(R) = +1)
    RtR = R.transpose().dot_mat(R)
    I = Mat3.identity()
    if (RtR - I).frob_norm() > 1e-4 or abs(R.det() - 1.0) > 1e-4:
        return False

    # 2. Camera 1 chirality: plane faces camera (n.z > 0 ensures positive depth along optical axis)
    if n.z <= 1e-5:
        return False

    # 3. Two-view depth: all observed image rays must have positive depth in both views
    for X in test_points:
        if X.z <= 0.0:
            return False
        # Normalized image ray x = X / X.z
        ray = X / X.z
        # Depth in camera 1: Z₁ = d / (n ⬝ ray) > 0  <=>  n ⬝ ray > 0
        n_ray = n.dot(ray)
        if n_ray <= 1e-6:
            return False

        # Ray transformed into camera 2: H ray = R ray + (n ⬝ ray) • t'
        ray2 = R.dot_vec(ray) + (t_prime * n_ray)
        # Depth in camera 2 must be positive: (H ray).z > 0
        if ray2.z <= 1e-6:
            return False

    return True


def filter_physical_solutions(
    solutions: list[HomographySolution],
    test_points: list[Vec3],
) -> list[HomographySolution]:
    """Filter candidate homography solutions by two-view chirality."""
    valid = []
    for sol in solutions:
        if satisfies_chirality(sol.R, sol.t_prime, sol.n, test_points):
            valid.append(sol)
    return valid
