"""World-frame rotating-base transport, redundant IK nullspace allocation, planar kinematics,
and real-time arrival-curve / response-time scheduling bounds.

Every public function is backed by a machine-checked theorem in
``Research.WorldFrameTransport``, ``RoboLean.Kinematics``, or ``RoboLean.RealTime``.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from fractions import Fraction
from typing import Any, TypeVar

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


def _is_frac_mode(*args: Any) -> bool:
    for arg in args:
        if arg is None:
            continue
        if isinstance(arg, Fraction):
            return True
        if isinstance(arg, (list, tuple)):
            for item in arg:
                if isinstance(item, Fraction):
                    return True
                if isinstance(item, (list, tuple)):
                    for sub in item:
                        if isinstance(sub, Fraction):
                            return True
    return False


def _coerce_vec(vec: Sequence[Any], use_frac: bool) -> list[Any]:
    return [Fraction(x) if use_frac else float(x) for x in vec]


def _coerce_mat(mat: Sequence[Any], n: int, m: int, use_frac: bool) -> list[list[Any]]:
    # Accept either 2D n x m sequence or 1D diagonal (when n == m) or flat n*m sequence
    if len(mat) == n and isinstance(mat[0], (list, tuple)) or hasattr(mat[0], "__len__"):
        rows = [
            [Fraction(mat[i][j]) if use_frac else float(mat[i][j]) for j in range(m)]
            for i in range(n)
        ]
        return rows
    if n == m and len(mat) == n:
        zero = Fraction(0) if use_frac else 0.0
        return [
            [
                (Fraction(mat[i]) if use_frac else float(mat[i])) if i == j else zero
                for j in range(m)
            ]
            for i in range(n)
        ]
    if len(mat) == n * m:
        return [
            [Fraction(mat[i * m + j]) if use_frac else float(mat[i * m + j]) for j in range(m)]
            for i in range(n)
        ]
    raise ValueError(f"Expected {n}x{m} matrix or diagonal vector, got length {len(mat)}.")


def _mat_vec(mat: list[list[Any]], vec: list[Any], use_frac: bool) -> list[Any]:
    zero = Fraction(0) if use_frac else 0.0
    return [
        sum((row[j] * vec[j] for j in range(len(vec))), zero)
        for row in mat
    ]


def _dot_vec(u: Sequence[Any], v: Sequence[Any], use_frac: bool) -> Any:
    zero = Fraction(0) if use_frac else 0.0
    return sum((x * y for x, y in zip(u, v, strict=True)), zero)


@lean_theorem(
    "ControlsLean.Robotics.ManipulatorTracking",
    (
        "trackingError",
        "referenceVel",
        "slidingError",
        "slidingError_eq_velError_add",
        "velError_eq_slidingError_sub",
    ),
    domain="kinematics_ik",
    summary=(
        "Slotine-Li virtual reference velocity qdot_r = qdot_d - Lambda q_tilde and "
        "composite sliding error s = qdot - qdot_r = qdot_tilde + Lambda q_tilde."
    ),
)
def slotine_li_sliding_error(
    q: Sequence[T],
    q_d: Sequence[T],
    qdot: Sequence[T],
    qdot_d: Sequence[T],
    lam_gains: Sequence[T] | Sequence[Sequence[T]],
) -> dict[str, Any]:
    """Compute Slotine-Li tracking error, virtual reference velocity, and sliding vector s.

    Supports both ``float`` and exact ``fractions.Fraction`` arithmetic. ``lam_gains`` may be
    supplied either as a length-n diagonal gain vector or as an n x n gain matrix ``Lambda``.
    """
    n = len(q)
    if n == 0 or len(q_d) != n or len(qdot) != n or len(qdot_d) != n:
        raise ValueError("Joint vectors q, q_d, qdot, qdot_d must be non-empty and equal length.")
    use_frac = _is_frac_mode(q, q_d, qdot, qdot_d, lam_gains)
    q_v = _coerce_vec(q, use_frac)
    qd_v = _coerce_vec(q_d, use_frac)
    dq_v = _coerce_vec(qdot, use_frac)
    dqd_v = _coerce_vec(qdot_d, use_frac)
    lam_m = _coerce_mat(lam_gains, n, n, use_frac)

    q_tilde = [q_v[i] - qd_v[i] for i in range(n)]
    qdot_tilde = [dq_v[i] - dqd_v[i] for i in range(n)]
    lam_q_tilde = _mat_vec(lam_m, q_tilde, use_frac)
    qdot_r = [dqd_v[i] - lam_q_tilde[i] for i in range(n)]
    s_vec = [dq_v[i] - qdot_r[i] for i in range(n)]
    s_alt = [qdot_tilde[i] + lam_q_tilde[i] for i in range(n)]
    zero = Fraction(0) if use_frac else 0.0
    equiv_res = max((abs(s_vec[i] - s_alt[i]) for i in range(n)), default=zero)

    return {
        "q_tilde": tuple(q_tilde),
        "qdot_tilde": tuple(qdot_tilde),
        "qdot_r": tuple(qdot_r),
        "s": tuple(s_vec),
        "kinematic_equivalence_residual": equiv_res,
    }


@lean_theorem(
    "ControlsLean.Robotics.ManipulatorTracking",
    (
        "slotineLiControl",
        "slotineLiAugmentedControl",
        "slotine_li_closed_loop_sliding",
        "skew_coriolis_power_cancel",
        "slotine_li_lyapunov_deriv",
        "slotine_li_lyapunov_deriv_nonpos",
        "slotine_li_exponential_rate",
    ),
    domain="kinematics_ik",
    summary=(
        "Slotine-Li passivity-based control torque tau = M qddot_r + C qdot_r + g - K_D s, "
        "skew-symmetric Coriolis cancellation, and kinetic sliding Lyapunov derivative."
    ),
)
def slotine_li_control_torque(
    m_mat: Sequence[Sequence[T]] | Sequence[T],
    c_mat: Sequence[Sequence[T]] | Sequence[T],
    kd_mat: Sequence[Sequence[T]] | Sequence[T],
    qdot_r: Sequence[T],
    qddot_r: Sequence[T],
    g_vec: Sequence[T],
    s_vec: Sequence[T],
    *,
    mdot_mat: Sequence[Sequence[T]] | Sequence[T] | None = None,
) -> dict[str, Any]:
    """Compute Slotine-Li control torque tau = M qddot_r + C qdot_r + g - K_D s and passivity metrics.

    Verifies the identities proved in ``ControlsLean.Robotics.ManipulatorTracking``:
    - ``skew_coriolis_power_cancel``: (1/2) s^T Mdot s == s^T C s when (Mdot - 2 C)^T == -(Mdot - 2 C)
    - ``slotine_li_lyapunov_deriv``: (1/2) s^T Mdot s + s^T (M sdot) == -s^T K_D s along M sdot + C s + K_D s == 0.
    """
    n = len(s_vec)
    if n == 0 or len(qdot_r) != n or len(qddot_r) != n or len(g_vec) != n:
        raise ValueError("Vectors qdot_r, qddot_r, g_vec, s_vec must be non-empty and equal length.")
    use_frac = _is_frac_mode(m_mat, c_mat, kd_mat, qdot_r, qddot_r, g_vec, s_vec, mdot_mat)
    m_m = _coerce_mat(m_mat, n, n, use_frac)
    c_m = _coerce_mat(c_mat, n, n, use_frac)
    kd_m = _coerce_mat(kd_mat, n, n, use_frac)
    dqr_v = _coerce_vec(qdot_r, use_frac)
    ddqr_v = _coerce_vec(qddot_r, use_frac)
    g_v = _coerce_vec(g_vec, use_frac)
    s_v = _coerce_vec(s_vec, use_frac)

    m_ddqr = _mat_vec(m_m, ddqr_v, use_frac)
    c_dqr = _mat_vec(c_m, dqr_v, use_frac)
    kd_s = _mat_vec(kd_m, s_v, use_frac)
    tau = [m_ddqr[i] + c_dqr[i] + g_v[i] - kd_s[i] for i in range(n)]

    c_s = _mat_vec(c_m, s_v, use_frac)
    coriolis_power = _dot_vec(s_v, c_s, use_frac)
    dissipation_power = -_dot_vec(s_v, kd_s, use_frac)

    # Along closed-loop error dynamics M sdot + C s + K_D s = 0, M sdot = -(C s + K_D s)
    m_sdot = [-(c_s[i] + kd_s[i]) for i in range(n)]
    s_dot_m_sdot = _dot_vec(s_v, m_sdot, use_frac)

    half = Fraction(1, 2) if use_frac else 0.5
    if mdot_mat is not None:
        mdot_m = _coerce_mat(mdot_mat, n, n, use_frac)
        mdot_s = _mat_vec(mdot_m, s_v, use_frac)
        half_mdot_quad = half * _dot_vec(s_v, mdot_s, use_frac)
    else:
        half_mdot_quad = coriolis_power

    skew_res = abs(half_mdot_quad - coriolis_power)
    lyap_deriv = half_mdot_quad + s_dot_m_sdot
    lyap_res = abs(lyap_deriv - dissipation_power)

    return {
        "tau": tuple(tau),
        "dissipation_power": dissipation_power,
        "coriolis_power": coriolis_power,
        "half_mdot_quad": half_mdot_quad,
        "skew_power_residual": skew_res,
        "lyapunov_deriv": lyap_deriv,
        "lyapunov_identity_residual": lyap_res,
    }


@lean_theorem(
    "ControlsLean.Robotics.ManipulatorTracking",
    (
        "slotine_li_adaptive_lyapunov_deriv",
        "skew_coriolis_power_cancel",
        "slotine_li_lyapunov_deriv",
    ),
    domain="kinematics_ik",
    summary=(
        "Slotine-Li adaptive parameter update theta_dot = -Gamma Y^T s and exact passivity "
        "cancellation of regressor parameter-estimation power."
    ),
)
def slotine_li_adaptive_update(
    y_reg: Sequence[Sequence[T]],
    gamma_gain: Sequence[Sequence[T]] | Sequence[T] | T,
    s_vec: Sequence[T],
    *,
    theta_tilde: Sequence[T] | None = None,
    kd_mat: Sequence[Sequence[T]] | Sequence[T] | None = None,
) -> dict[str, Any]:
    """Compute Slotine-Li adaptive parameter update rate ``theta_dot = -Gamma Y^T s``.

    Verifies ``ControlsLean.Robotics.ManipulatorTracking.slotine_li_adaptive_lyapunov_deriv``:
    under ``Gamma^{-1} theta_dot_tilde = -Y^T s`` and ``M sdot + C s + K_D s = Y theta_tilde``,
    the parameter error power ``theta_tilde^T (Gamma^{-1} theta_dot_tilde)`` cancels the
    regressor mismatch power ``s^T (Y theta_tilde)`` identically.
    """
    n = len(s_vec)
    if n == 0 or len(y_reg) != n or len(y_reg[0]) == 0:
        raise ValueError("Regressor matrix y_reg must have shape (n, p) matching s_vec.")
    p = len(y_reg[0])
    use_frac = _is_frac_mode(y_reg, gamma_gain, s_vec, theta_tilde, kd_mat)
    y_m = _coerce_mat(y_reg, n, p, use_frac)
    s_v = _coerce_vec(s_vec, use_frac)

    if isinstance(gamma_gain, (int, float, Fraction)):
        g_scalar = Fraction(gamma_gain) if use_frac else float(gamma_gain)
        zero = Fraction(0) if use_frac else 0.0
        gamma_m = [[g_scalar if i == j else zero for j in range(p)] for i in range(p)]
    else:
        gamma_m = _coerce_mat(gamma_gain, p, p, use_frac)

    # Compute Y^T s and Gamma^{-1} theta_dot = -Y^T s
    zero = Fraction(0) if use_frac else 0.0
    yt_s = [sum((y_m[i][j] * s_v[i] for i in range(n)), zero) for j in range(p)]
    gamma_inv_theta_dot = [-val for val in yt_s]
    theta_dot = _mat_vec(gamma_m, gamma_inv_theta_dot, use_frac)

    reg_power: Any = zero
    adapt_power: Any = zero
    cancel_res: Any = zero
    if theta_tilde is not None:
        if len(theta_tilde) != p:
            raise ValueError("theta_tilde must have length p.")
        th_v = _coerce_vec(theta_tilde, use_frac)
        y_th = _mat_vec(y_m, th_v, use_frac)
        reg_power = _dot_vec(s_v, y_th, use_frac)
        adapt_power = _dot_vec(th_v, gamma_inv_theta_dot, use_frac)
        cancel_res = abs(reg_power + adapt_power)

    dissip_power: Any = zero
    if kd_mat is not None:
        kd_m = _coerce_mat(kd_mat, n, n, use_frac)
        kd_s = _mat_vec(kd_m, s_v, use_frac)
        dissip_power = -_dot_vec(s_v, kd_s, use_frac)

    return {
        "theta_dot": tuple(theta_dot),
        "gamma_inv_theta_dot": tuple(gamma_inv_theta_dot),
        "regressor_power": reg_power,
        "adaptation_power": adapt_power,
        "passivity_cancellation_residual": cancel_res,
        "adaptive_lyapunov_deriv": dissip_power + reg_power + adapt_power,
    }

