"""Planar homography decomposition, Faugeras-Lustman unit singular value sandwich,
two-view triangulation, and 6-DOF SE(3) homography-based visual servoing (HBVS).

Every public function is backed by a machine-checked theorem in
``Research.HomographyDecomposition``, ``Research.VisualServoingInvariant``, or
``ControlsLean.Vision.Triangulation``.
"""

from __future__ import annotations

import math
from fractions import Fraction
from typing import TypeVar

from ctrl.robotics.contact_cbf import Vec3T, add3, cross3, dot3, smul3, sub3
from ctrl.robotics.kinematics_ik import sq_norm3
from ctrl.robotics.registry import lean_theorem

T = TypeVar("T", float, Fraction)


@lean_theorem(
    "Research.HomographyDecomposition",
    ("gramHomographyVec", "gram_homography_quad_form", "homography_gram_unit_eigenvector"),
    domain="vision_se3",
    summary="Action of planar homography Gram operator G = H^T H on x in R^3, fixing n x v.",
)
def gram_homography_vec(n: Vec3T[T], v: Vec3T[T], x: Vec3T[T]) -> Vec3T[T]:
    """Compute G(x) = x + (v.x) n + (n.x) v + ((n.x) ||v||^2) n."""
    vx = dot3(v, x)
    nx = dot3(n, x)
    v_sq = sq_norm3(v)
    c_n = vx + nx * v_sq
    return add3(add3(x, smul3(c_n, n)), smul3(nx, v))


@lean_theorem(
    "Research.HomographyDecomposition",
    ("homography_gram_unit_eigenvector", "homography_singular_value_sandwich"),
    domain="vision_se3",
    summary="Faugeras-Lustman unit singular vector w = n x v and Lagrange sandwich identity.",
)
def verify_homography_singular_sandwich(n: Vec3T[T], v: Vec3T[T]) -> dict[str, T | Vec3T[T] | bool]:
    """Verify G(n x v) == n x v and (sigma_1^2 - 1)(1 - sigma_3^2) == ||n x v||^2."""
    two: T = Fraction(2, 1) if isinstance(n[0], Fraction) else 2.0  # type: ignore[assignment]
    one: T = Fraction(1, 1) if isinstance(n[0], Fraction) else 1.0  # type: ignore[assignment]
    w = cross3(n, v)
    gw = gram_homography_vec(n, v, w)
    nv = dot3(n, v)
    tr_2d = two + two * nv + sq_norm3(v)
    det_2d = (one + nv) ** 2
    sandwich_prod = tr_2d - det_2d - one
    w_sq = sq_norm3(w)
    return {
        "unit_eigenvector": w,
        "gram_image": gw,
        "sandwich_product": sandwich_prod,
        "cross_sq_norm": w_sq,
        "is_exact": gw == w and sandwich_prod == w_sq,
    }


@lean_theorem(
    "Research.HomographyDecomposition",
    (
        "allSignTriples",
        "survivingSignTriples",
        "eliminatedSignTriples",
        "candidate_reproduces_homography",
        "ground_truth_satisfies_chirality",
        "elimination_theorem",
        "eliminated_solutions_fail_chirality",
        "solution_count_equality",
    ),
    domain="vision_se3",
    summary="Faugeras 8-branch sign triple enumeration and two-view chirality elimination (8 -> 2).",
)
def filter_faugeras_chirality_branches(
    n_a_dot_x: T,
    n_a_dot_hx: T,
    n_b_dot_x: T,
    n_b_dot_hx: T,
) -> list[tuple[int, int, int]]:
    """Filter all 8 Faugeras sign triples (eps1, eps2, eps3) in {-1, +1}^3 by proper pose + chirality."""
    surviving: list[tuple[int, int, int]] = []
    for eps1 in (1, -1):
        for eps2 in (1, -1):
            for eps3 in (1, -1):
                proper_pose = (eps2 * eps3) == 1
                if eps1 == 1:
                    c1 = eps3 * n_a_dot_x > 0
                    c2 = eps3 * n_a_dot_hx > 0
                else:
                    c1 = eps3 * n_b_dot_x > 0
                    c2 = eps3 * n_b_dot_hx > 0
                if proper_pose and c1 and c2:
                    surviving.append((eps1, eps2, eps3))
    return surviving


@lean_theorem(
    "Research.VisualServoingInvariant",
    (
        "se3_depth_hasDerivAt",
        "se3_normal_sqNorm_hasDerivAt",
        "se3_depth_positive_of_feedback",
        "visual_servoing_depth_positive",
        "closed_loop_depth_formula",
    ),
    domain="vision_se3",
    summary="6-DOF SE(3) rotational depth cancellation and HBVS exponential depth lower bound.",
)
def se3_depth_derivative(
    x_c: Vec3T[T], n_c: Vec3T[T], v_cam: Vec3T[T], omega_cam: Vec3T[T]
) -> dict[str, T]:
    """Compute d/dt (n_c . X_c) under 6-DOF SE(3) twist (v_cam, omega_cam).

    Proves that the rotational Lie derivative (-omega x n_c) . X_c + n_c . (-omega x X_c)
    vanishes identically, so d/dt d(t) = -n_c . v_cam.
    """
    neg_omega = smul3(
        Fraction(-1, 1) if isinstance(x_c[0], Fraction) else -1.0,  # type: ignore[arg-type]
        omega_cam,
    )
    dn_c = cross3(neg_omega, n_c)
    dx_c = sub3(cross3(neg_omega, x_c), v_cam)
    rot_term = dot3(dn_c, x_c) + dot3(n_c, cross3(neg_omega, x_c))
    total_deriv = dot3(dn_c, x_c) + dot3(n_c, dx_c)
    trans_only = -dot3(n_c, v_cam)
    return {
        "rotational_lie_derivative": rot_term,
        "total_depth_derivative": total_deriv,
        "translational_formula": trans_only,
    }


@lean_theorem(
    "Research.VisualServoingInvariant",
    ("chaumette_retreat_unbounded", "visual_servoing_depth_positive", "se3_depth_positive_of_feedback"),
    domain="vision_se3",
    summary="Compare 6-DOF HBVS positive depth invariance against Chaumette IBVS camera retreat.",
)
def hbvs_vs_ibvs_depth_ratio(
    d0: float, d_star: float, lam: float, t: float, delta_phi_rad: float
) -> dict[str, float]:
    """Compute HBVS depth d_HBVS(t) vs. classical IBVS apparent depth scale under optical rotation."""
    w = math.exp(-lam * t)
    d_hbvs = w * d0 + (1.0 - w) * d_star
    cos_half = math.cos(delta_phi_rad / 2.0)
    ibvs_midpoint_depth = d_star / max(abs(cos_half), 1e-6)
    return {
        "d_hbvs": d_hbvs,
        "ibvs_midpoint_depth": ibvs_midpoint_depth,
        "hbvs_stays_bounded": min(d0, d_star) - 1e-12 <= d_hbvs <= max(d0, d_star) + 1e-12,
    }


@lean_theorem(
    "ControlsLean.Vision.Triangulation",
    (
        "depth₁_eq",
        "depth₂_eq",
        "depths_unique",
        "scene_closedForm",
        "exists_depths_iff",
        "cheirality",
    ),
    domain="vision_se3",
    summary="Closed-form two-view ray triangulation depths (d1, d2) and cheirality sign resolution.",
)
def triangulate_two_view_rays(
    r_x1: Vec3T[T], x2: Vec3T[T], t_vec: Vec3T[T]
) -> tuple[T, T]:
    """Compute unique closed-form depths (d1, d2) solving d2 * x2 = d1 * (R x1) + t."""
    n_vec = cross3(x2, r_x1)
    denom = sq_norm3(n_vec)
    if denom == 0:
        raise ValueError("Rays x2 and R x1 are parallel (n = x2 x R x1 = 0).")
    d1 = -dot3(n_vec, cross3(x2, t_vec)) / denom
    d2 = -dot3(n_vec, cross3(r_x1, t_vec)) / denom
    return d1, d2
