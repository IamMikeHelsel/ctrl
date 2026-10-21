"""World-frame rotating-base transport, redundant IK nullspace allocation, planar kinematics,
and real-time arrival-curve / response-time scheduling bounds.

Every public function is backed by a machine-checked theorem in
``Research.WorldFrameTransport``, ``RoboLean.Kinematics``, or ``RoboLean.RealTime``.
"""

from __future__ import annotations

import math
from fractions import Fraction
from typing import TypeVar

from ctrl.robotics.contact_cbf import Vec3T, add3, cross3, dot3, smul3, sub3
from ctrl.robotics.registry import lean_theorem

T = TypeVar("T", float, Fraction)


def sq_norm3(u: Vec3T[T]) -> T:
    return u[0] * u[0] + u[1] * u[1] + u[2] * u[2]


@lean_theorem(
    "Research.WorldFrameTransport",
    ("eulerAccel", "euler_centripetal_orthogonal"),
    domain="kinematics_ik",
    summary="Euler tangential acceleration alpha x p = (ddtheta * k_hat) x p.",
)
def euler_accel(k_hat: Vec3T[T], p: Vec3T[T], ddtheta: T) -> Vec3T[T]:
    """Compute Euler tangential acceleration (ddtheta * k_hat) x p."""
    return cross3(smul3(ddtheta, k_hat), p)


@lean_theorem(
    "Research.WorldFrameTransport",
    ("centripetalAccel", "euler_centripetal_orthogonal"),
    domain="kinematics_ik",
    summary="Centripetal acceleration omega x (omega x p).",
)
def centripetal_accel(k_hat: Vec3T[T], p: Vec3T[T], dtheta: T) -> Vec3T[T]:
    """Compute centripetal acceleration (dtheta * k_hat) x ((dtheta * k_hat) x p)."""
    omega = smul3(dtheta, k_hat)
    return cross3(omega, cross3(omega, p))


@lean_theorem(
    "Research.WorldFrameTransport",
    (
        "worldFrameAccel",
        "euler_centripetal_orthogonal",
        "euler_centripetal_sqNorm_exact",
        "body_hold_violates_world_accel",
    ),
    domain="kinematics_ik",
    summary="Full world-frame acceleration a_W = a_B + 2(omega x v_B) + alpha x p + omega x (omega x p).",
)
def world_frame_accel(
    a_b: Vec3T[T],
    v_b: Vec3T[T],
    k_hat: Vec3T[T],
    p: Vec3T[T],
    dtheta: T,
    ddtheta: T,
) -> Vec3T[T]:
    """Compute full 3D world-frame acceleration on a rotating base."""
    two: T = Fraction(2, 1) if isinstance(dtheta, Fraction) else 2.0  # type: ignore[assignment]
    coriolis = smul3(two, cross3(smul3(dtheta, k_hat), v_b))
    a_eul = euler_accel(k_hat, p, ddtheta)
    a_cent = centripetal_accel(k_hat, p, dtheta)
    return add3(add3(a_b, coriolis), add3(a_eul, a_cent))


@lean_theorem(
    "Research.WorldFrameTransport",
    ("euler_centripetal_orthogonal", "euler_centripetal_sqNorm_exact"),
    domain="kinematics_ik",
    summary="Exact Pythagorean identity ||alpha x p + omega x (omega x p)||^2 = (ddtheta^2 + dtheta^4)||k_hat x p||^2.",
)
def rotational_transport_sq_norm(k_hat: Vec3T[T], p: Vec3T[T], dtheta: T, ddtheta: T) -> T:
    """Compute exact squared norm of combined Euler + centripetal transport acceleration."""
    return (ddtheta * ddtheta + (dtheta**4)) * sq_norm3(cross3(k_hat, p))


@lean_theorem(
    "Research.WorldFrameTransport",
    (
        "minimalInterventionAlloc",
        "minimal_intervention_achieves_task",
        "minimal_intervention_preserves_nullspace",
        "minimal_intervention_pythagorean_optimality",
    ),
    domain="kinematics_ik",
    summary="Moore-Penrose minimal-intervention joint velocity allocation q* on redundant arms.",
)
def minimal_intervention_ik(j_row: Vec3T[T], q_nom: Vec3T[T], v_task: T) -> Vec3T[T]:
    """Compute q* = q_nom + ((v_task - J . q_nom) / ||J||^2) J."""
    j_sq = sq_norm3(j_row)
    if j_sq == 0:
        raise ValueError("Task Jacobian row j_row must be non-zero.")
    scale = (v_task - dot3(j_row, q_nom)) / j_sq
    return add3(q_nom, smul3(scale, j_row))


@lean_theorem(
    "Research.WorldFrameTransport",
    ("minimal_intervention_pythagorean_optimality",),
    domain="kinematics_ik",
    summary="Verify Pythagorean decomposition ||q - q_nom||^2 = ||q* - q_nom||^2 + ||q - q*||^2.",
)
def verify_pythagorean_ik_optimality(
    j_row: Vec3T[T], q_nom: Vec3T[T], q_alt: Vec3T[T], v_task: T
) -> dict[str, T]:
    """Compute exact Pythagorean optimality decomposition for any task-feasible q_alt."""
    q_star = minimal_intervention_ik(j_row, q_nom, v_task)
    lhs = sq_norm3(sub3(q_alt, q_nom))
    star_norm = sq_norm3(sub3(q_star, q_nom))
    diff_norm = sq_norm3(sub3(q_alt, q_star))
    return {
        "lhs_sq_norm": lhs,
        "rhs_sum": star_norm + diff_norm,
        "star_sq_norm": star_norm,
        "residual_sq_norm": diff_norm,
    }


@lean_theorem(
    "RoboLean.Kinematics",
    (
        "fkX",
        "fkY",
        "fkX_sq_add_fkY_sq",
        "norm_fk_le",
        "abs_sub_le_norm_fk",
        "exists_fk_eq",
        "range_fk",
        "det_jacobian",
        "det_jacobian_eq_zero_iff_boundary",
    ),
    domain="kinematics_ik",
    summary="Two-link planar arm forward kinematics, annulus workspace, and Jacobian determinant.",
)
def two_link_fk_and_jacobian(
    l1: float, l2: float, q1: float, q2: float
) -> dict[str, float | bool]:
    """Compute 2-link planar arm end-effector (x, y), radius^2, and Jacobian determinant."""
    x = l1 * math.cos(q1) + l2 * math.cos(q1 + q2)
    y = l1 * math.sin(q1) + l2 * math.sin(q1 + q2)
    r_sq = x * x + y * y
    r_norm = math.sqrt(r_sq)
    det_j = l1 * l2 * math.sin(q2)
    in_annulus = abs(l1 - l2) - 1e-12 <= r_norm <= (l1 + l2) + 1e-12
    return {
        "x": x,
        "y": y,
        "r_sq": r_sq,
        "r_sq_cosine_law": l1 * l1 + l2 * l2 + 2.0 * l1 * l2 * math.cos(q2),
        "det_jacobian": det_j,
        "in_annulus": in_annulus,
    }


@lean_theorem(
    "Research.WorldFrameTransport",
    ("minimum_spacing_queue_bound", "dense_future_events_in_window"),
    domain="kinematics_ik",
    summary="Arrival-curve minimum-spacing queue capacity bound N * delta <= H.",
)
def max_retained_events(horizon: T, min_spacing: T) -> int:
    """Return the exact upper bound floor(H / delta) + 1 on retained events in [t0, t0 + H]."""
    if min_spacing <= 0:
        raise ValueError("min_spacing must be strictly positive.")
    return int(horizon // min_spacing) + 1


@lean_theorem(
    "RoboLean.RealTime",
    (
        "cdiv",
        "interference",
        "rtaStep",
        "rta",
        "rta_sound",
        "rta_none",
        "rta_isSome_iff",
        "rm_two_tasks_schedulable",
        "edf_schedulable_iff",
    ),
    domain="kinematics_ik",
    summary="Joseph-Pandya / Audsley fixed-priority response-time analysis (RTA).",
)
def response_time_analysis(
    wcet: int, higher_priority_tasks: list[tuple[int, int]], deadline: int
) -> int | None:
    """Compute exact worst-case response time R <= D via Joseph-Pandya iteration, or None."""
    r = wcet
    for _ in range(deadline + 1):
        if r > deadline:
            return None
        interf = sum(((r + t_j - 1) // t_j) * c_j for c_j, t_j in higher_priority_tasks)
        r_next = wcet + interf
        if r_next == r:
            return r
        r = r_next
    return None
