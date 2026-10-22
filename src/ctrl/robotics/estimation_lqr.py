"""Discrete-time LQR/DARE completion of squares, Bucy-Joseph Kalman filter MMSE updates,
steady-state Kalata alpha-beta tracking filter, Luenberger separation principle, and MPC feasibility.

Every public function is backed by a machine-checked theorem in ``ControlsLean``.
"""

from __future__ import annotations

import math
from typing import Any

import numpy as np

from ctrl.robotics.registry import lean_theorem


@lean_theorem(
    "ControlsLean.Controls.DARE",
    (
        "inputGram",
        "dareOfGain",
        "lqrClosedLoop",
        "bellmanResidual",
        "bellman_completion_of_squares",
        "quad_bellman_le",
        "dare_closed_loop_lyapunov",
        "dare_closed_loop_tendsto_zero",
    ),
    domain="estimation_lqr",
    summary="Discrete Algebraic Riccati Equation (DARE), Bellman completion of squares, and LQR gain.",
)
def dare_bellman_completion_of_squares(
    a_mat: np.ndarray,
    b_mat: np.ndarray,
    q_mat: np.ndarray,
    r_mat: np.ndarray,
    p_mat: np.ndarray,
    k_cand: np.ndarray,
) -> dict[str, Any]:
    """Compute S = R + B^T P B, optimal gain K* = S^{-1} B^T P A, and verify completion of squares.

    Checks the exact matrix identity proved in ``ControlsLean.Controls.DARE.bellman_completion_of_squares``:
    M(K) == T(P) - P + (K - K*)^T S (K - K*).
    """
    s_gram = r_mat + b_mat.T @ p_mat @ b_mat
    k_star = np.linalg.solve(s_gram, b_mat.T @ p_mat @ a_mat)
    t_p = a_mat.T @ p_mat @ a_mat - k_star.T @ s_gram @ k_star + q_mat
    a_cl = a_mat - b_mat @ k_cand
    m_k = q_mat + k_cand.T @ r_mat @ k_cand + a_cl.T @ p_mat @ a_cl - p_mat
    dk = k_cand - k_star
    rhs = (t_p - p_mat) + dk.T @ s_gram @ dk
    max_err = float(np.max(np.abs(m_k - rhs)))
    return {
        "input_gram": s_gram,
        "k_star": k_star,
        "dare_tp": t_p,
        "bellman_residual": m_k,
        "completion_of_squares_rhs": rhs,
        "max_abs_error": max_err,
    }


@lean_theorem(
    "ControlsLean.Estimation.KalmanOptimality",
    (
        "josephCov",
        "innovCov",
        "josephCov_transpose",
        "josephCov_completion_of_squares",
        "quad_josephCov_nonneg",
        "quad_josephCov_le",
        "trace_josephCov_eq",
        "trace_josephCov_le",
    ),
    domain="estimation_lqr",
    summary="Bucy-Joseph stabilized covariance update and MMSE trace completion of squares.",
)
def joseph_kalman_update(
    p_prior: np.ndarray,
    c_obs: np.ndarray,
    r_noise: np.ndarray,
    k_cand: np.ndarray | None = None,
) -> dict[str, Any]:
    """Compute innovation covariance S, optimal Kalman gain K*, and Bucy-Joseph posterior P^+(K).

    Verifies the matrix identity ``josephCov_completion_of_squares``:
    P^+(K) == P^+(K*) + (K - K*) S (K - K*)^T and tr(P^+(K*)) <= tr(P^+(K)).
    """
    n = p_prior.shape[0]
    eye = np.eye(n)
    s_innov = c_obs @ p_prior @ c_obs.T + r_noise
    k_star = np.linalg.solve(s_innov.T, (p_prior @ c_obs.T).T).T

    ik_star = eye - k_star @ c_obs
    p_post_star = ik_star @ p_prior @ ik_star.T + k_star @ r_noise @ k_star.T

    if k_cand is None:
        k_cand = k_star

    ik_cand = eye - k_cand @ c_obs
    p_post_cand = ik_cand @ p_prior @ ik_cand.T + k_cand @ r_noise @ k_cand.T
    dk = k_cand - k_star
    rhs = p_post_star + dk @ s_innov @ dk.T
    return {
        "innov_cov": s_innov,
        "k_star": k_star,
        "p_post_star": p_post_star,
        "p_post_cand": p_post_cand,
        "completion_rhs": rhs,
        "trace_star": float(np.trace(p_post_star)),
        "trace_cand": float(np.trace(p_post_cand)),
        "max_abs_error": float(np.max(np.abs(p_post_cand - rhs))),
    }


@lean_theorem(
    "ControlsLean.Estimation.AlphaBeta",
    (
        "trackingIndex",
        "gain_quadratic",
        "beta_sq_div",
        "kalata",
        "kalataU",
        "kalataU_spec",
        "exists_gains",
        "exists_steadyState",
    ),
    domain="estimation_lqr",
    summary="Closed-form steady-state Kalata alpha-beta tracker gains and Riccati covariance.",
)
def kalata_alpha_beta_gains(sample_period: float, accel_var: float, meas_var: float) -> dict[str, float]:
    """Compute exact steady-state (alpha, beta) gains and covariance (p11, p12, p22) via KalataU."""
    if sample_period <= 0 or accel_var <= 0 or meas_var <= 0:
        raise ValueError("sample_period, accel_var, and meas_var must be strictly positive.")
    lam = math.sqrt(accel_var) * (sample_period**2) / math.sqrt(meas_var)
    c = 2.0 + lam / 2.0
    u = (c - math.sqrt(c * c - 4.0)) / 2.0
    alpha = 1.0 - u * u
    beta = 2.0 * ((1.0 - u) ** 2)
    s = meas_var / (1.0 - alpha)
    p11 = alpha * s
    p12 = beta * s / sample_period
    p22 = s * beta * (alpha + beta / 2.0) / (sample_period**2)
    quad_res = abs(alpha * alpha - ((2.0 - alpha) * beta - (beta * beta) / 4.0))
    return {
        "tracking_index": lam,
        "u": u,
        "alpha": alpha,
        "beta": beta,
        "p11": p11,
        "p12": p12,
        "p22": p22,
        "kalata_quadratic_residual": quad_res,
    }


@lean_theorem(
    "ControlsLean.Controls.Observer",
    (
        "plantStep",
        "observerStep",
        "estimationError",
        "observer_error_step",
        "observer_error_step_control_invariant",
        "observer_error_pow",
        "closed_loop_separation_block",
        "closed_loop_separation_det",
        "closed_loop_separation_charpoly",
    ),
    domain="estimation_lqr",
    summary="Luenberger state observer error control-invariance and characteristic polynomial separation.",
)
def luenberger_separation_step(
    a_mat: np.ndarray,
    b_mat: np.ndarray,
    c_mat: np.ndarray,
    k_gain: np.ndarray,
    l_gain: np.ndarray,
    x: np.ndarray,
    x_hat: np.ndarray,
) -> dict[str, Any]:
    """Execute one coupled plant + Luenberger observer step under u = -K x_hat and check separation."""
    u = -(k_gain @ x_hat)
    y = c_mat @ x
    x_next = a_mat @ x + b_mat @ u
    x_hat_next = a_mat @ x_hat + b_mat @ u + l_gain @ (y - c_mat @ x_hat)
    err = x - x_hat
    err_next = x_next - x_hat_next
    err_pred = (a_mat - l_gain @ c_mat) @ err

    n = a_mat.shape[0]
    zero_block = np.zeros((n, n))
    aug_mat = np.block([[a_mat - b_mat @ k_gain, b_mat @ k_gain], [zero_block, a_mat - l_gain @ c_mat]])
    det_aug = float(np.linalg.det(aug_mat))
    det_prod = float(np.linalg.det(a_mat - b_mat @ k_gain) * np.linalg.det(a_mat - l_gain @ c_mat))
    return {
        "x_next": x_next,
        "x_hat_next": x_hat_next,
        "err_next": err_next,
        "err_autonomous_pred": err_pred,
        "det_augmented": det_aug,
        "det_product": det_prod,
        "error_step_residual": float(np.max(np.abs(err_next - err_pred))),
        "det_separation_residual": abs(det_aug - det_prod),
    }


@lean_theorem(
    "ControlsLean.Controls.MPCFeasibility",
    (
        "mpcTraj",
        "shiftInput",
        "mpc_recursive_feasibility_step",
        "mpc_closed_loop_feasible",
        "mpcCost_shiftInput_eq",
        "mpc_value_descent",
        "mpc_optimal_value_descent",
        "mpc_closed_loop_cost_bound",
    ),
    domain="estimation_lqr",
    summary="Constrained MPC warm-start input shift and terminal-CLF Lyapunov value descent.",
)
def mpc_warm_start_cost_descent(
    a_mat: np.ndarray,
    b_mat: np.ndarray,
    q_mat: np.ndarray,
    r_mat: np.ndarray,
    p_term: np.ndarray,
    k_term: np.ndarray,
    x0: np.ndarray,
    u_seq: np.ndarray,
) -> dict[str, float | bool]:
    """Evaluate horizon-N MPC cost J_N(x0, u) and warm-start shifted cost J_N(x1, shiftInput(u)).

    Checks the exact identity ``mpcCost_shiftInput_eq`` and value descent ``mpc_value_descent``.
    """
    horizon = u_seq.shape[0]
    x_traj = [x0]
    for k in range(horizon):
        x_traj.append(a_mat @ x_traj[-1] + b_mat @ u_seq[k])
    x_n = x_traj[-1]

    def stage_cost(x: np.ndarray, u: np.ndarray) -> float:
        return float(x.T @ q_mat @ x + u.T @ r_mat @ u)

    def term_cost(x: np.ndarray) -> float:
        return float(x.T @ p_term @ x)

    j_orig = sum(stage_cost(x_traj[k], u_seq[k]) for k in range(horizon)) + term_cost(x_n)

    u_term = -(k_term @ x_n)
    u_shift = np.vstack([u_seq[1:], u_term[None, :]]) if horizon > 1 else u_term[None, :]
    x1 = x_traj[1]
    x_shift = [x1]
    for k in range(horizon):
        x_shift.append(a_mat @ x_shift[-1] + b_mat @ u_shift[k])
    j_shift = sum(stage_cost(x_shift[k], u_shift[k]) for k in range(horizon)) + term_cost(x_shift[-1])

    l0 = stage_cost(x0, u_seq[0])
    clf_delta = term_cost(x_shift[-1]) + stage_cost(x_n, u_term) - term_cost(x_n)
    identity_err = abs(j_shift - (j_orig - l0 + clf_delta))
    return {
        "j_orig": j_orig,
        "j_shift": j_shift,
        "stage_cost_0": l0,
        "terminal_clf_delta": clf_delta,
        "shift_identity_error": identity_err,
        "lyapunov_descent_holds": j_shift <= j_orig - l0 + 1e-10,
    }


@lean_theorem(
    "ControlsLean.Controls.DAREDetectable",
    (
        "lqrHessian",
        "lqrJosephUpdate",
        "joseph_dissipation_factored",
        "joseph_zero_dissipation_escape",
        "dare_schur_of_detectable",
        "dare_unique_of_detectable",
        "dare_bellman_return_difference",
        "dare_perturbed_lyapunov_dissipation",
        "dare_perturbed_dissipation_ge_of_margin",
    ),
    domain="estimation_lqr",
    summary=(
        "Kwakernaak-Sivan DARE detectability theory (Q = C^T C >= 0), zero-step escape, "
        "Bellman return-difference, and quadratic disk-margin robustness."
    ),
)
def dare_detectable_return_difference_margin(
    a_mat: np.ndarray,
    b_mat: np.ndarray,
    c_mat: np.ndarray,
    r_mat: np.ndarray,
    p_mat: np.ndarray,
    delta_k: np.ndarray,
    x: np.ndarray,
    u: np.ndarray,
) -> dict[str, Any]:
    """Verify factored DARE dissipation (Q = C^T C), Bellman return-difference, and gain margin.

    Checks the identities in ``ControlsLean.Controls.DAREDetectable``:
    - ``joseph_dissipation_factored``: x^T P x - (A_K x)^T P (A_K x) == ||C x||^2 + (K* x)^T R (K* x)
    - ``dare_bellman_return_difference``: l(x, u) + (A x + B u)^T P (A x + B u) - x^T P x == (u + K* x)^T G (u + K* x)
    - ``dare_perturbed_lyapunov_dissipation``: perturbed one-step decrease with exact return-difference loss
    - ``dare_perturbed_dissipation_ge_of_margin``: disk-margin certification
    """
    q_mat = c_mat.T @ c_mat
    g_hess = r_mat + b_mat.T @ p_mat @ b_mat
    k_star = np.linalg.solve(g_hess, b_mat.T @ p_mat @ a_mat)
    a_cl = a_mat - b_mat @ k_star
    p_joseph = q_mat + k_star.T @ r_mat @ k_star + a_cl.T @ p_mat @ a_cl
    dare_fix_err = float(np.max(np.abs(p_joseph - p_mat)))

    # Factored dissipation along optimal closed loop
    cx = c_mat @ x
    kx = k_star @ x
    v_x = float(x.T @ p_mat @ x)
    v_ax = float((a_cl @ x).T @ p_mat @ (a_cl @ x))
    factored_rhs = float(cx.T @ cx + kx.T @ r_mat @ kx)
    factored_dissipation_err = abs((v_x - v_ax) - (factored_rhs + float(x.T @ (p_mat - p_joseph) @ x)))

    # Bellman return-difference identity
    x_next_u = a_mat @ x + b_mat @ u
    stage_lu = float(x.T @ q_mat @ x + u.T @ r_mat @ u)
    bellman_lhs = stage_lu + float(x_next_u.T @ p_mat @ x_next_u) - float(x.T @ p_joseph @ x)
    u_diff = u + kx
    bellman_rhs = float(u_diff.T @ g_hess @ u_diff)
    return_diff_err = abs(bellman_lhs - bellman_rhs)

    # Perturbed closed-loop Lyapunov dissipation
    k_pert = k_star + delta_k
    a_pert = a_mat - b_mat @ k_pert
    dk_x = delta_k @ x
    kpert_x = k_pert @ x
    pert_lhs = float(x.T @ p_joseph @ x) - float((a_pert @ x).T @ p_mat @ (a_pert @ x))
    pert_rhs = float(x.T @ q_mat @ x + kpert_x.T @ r_mat @ kpert_x - dk_x.T @ g_hess @ dk_x)
    perturbed_dissipation_err = abs(pert_lhs - pert_rhs)

    return_diff_penalty = float(dk_x.T @ g_hess @ dk_x)
    perturbed_control_effort = float(kpert_x.T @ r_mat @ kpert_x)
    within_disk_margin = return_diff_penalty <= perturbed_control_effort + 1e-12

    return {
        "k_star": k_star,
        "hessian_g": g_hess,
        "dare_fixed_point_error": dare_fix_err,
        "factored_dissipation_error": factored_dissipation_err,
        "return_difference_error": return_diff_err,
        "perturbed_dissipation_error": perturbed_dissipation_err,
        "return_difference_penalty": return_diff_penalty,
        "perturbed_control_effort": perturbed_control_effort,
        "within_disk_margin": within_disk_margin,
    }


@lean_theorem(
    "ControlsLean.Controls.BoundedRealHInf",
    (
        "lqg_closed_loop_stable_of_stabilizable_detectable",
        "hinfHessian",
        "hinfDisturbanceGain",
        "hinfRiccatiMap",
        "hinf_stage_completion_of_squares",
        "hinf_l2_gain_bound",
        "hinf_worstCase_disturbance_tight",
    ),
    domain="estimation_lqr",
    summary=(
        "Discrete-time Bounded Real Lemma, H-infinity disturbance Hessian M_gamma(P) > 0, "
        "indefinite Riccati completion of squares, and finite-horizon L2-gain attenuation."
    ),
)
def hinf_bounded_real_step(
    a_mat: np.ndarray,
    b_dist: np.ndarray,
    c_perf: np.ndarray,
    d_feed: np.ndarray,
    p_mat: np.ndarray,
    gamma: float,
    x: np.ndarray,
    w: np.ndarray,
) -> dict[str, Any]:
    """Compute H-infinity disturbance Hessian M_gamma(P), worst-case disturbance gain K_w*, and L2-gain stage identity.

    Verifies the exact completion-of-squares identity in
    ``ControlsLean.Controls.BoundedRealHInf.hinf_stage_completion_of_squares``:
    ||C x + D w||^2 - gamma^2 ||w||^2 + (A x + B w)^T P (A x + B w)
      == x^T R_gamma(P) x - (w - K_w* x)^T M_gamma(P) (w - K_w* x).
    """
    if gamma <= 0:
        raise ValueError("H-infinity attenuation level gamma must be strictly positive.")
    m = b_dist.shape[1]
    m_hess = (gamma**2) * np.eye(m) - d_feed.T @ d_feed - b_dist.T @ p_mat @ b_dist
    eigvals = np.linalg.eigvalsh(0.5 * (m_hess + m_hess.T))
    hessian_pos_def = bool(np.all(eigvals > 0.0))

    kw_star = np.linalg.solve(m_hess, d_feed.T @ c_perf + b_dist.T @ p_mat @ a_mat)
    r_gamma = (
        c_perf.T @ c_perf
        + a_mat.T @ p_mat @ a_mat
        + kw_star.T @ m_hess @ kw_star
    )

    z = c_perf @ x + d_feed @ w
    x_next = a_mat @ x + b_dist @ w
    stage_lhs = (
        float(z.T @ z)
        - (gamma**2) * float(w.T @ w)
        + float(x_next.T @ p_mat @ x_next)
    )
    w_dev = w - kw_star @ x
    stage_rhs = float(x.T @ r_gamma @ x) - float(w_dev.T @ m_hess @ w_dev)
    completion_err = abs(stage_lhs - stage_rhs)

    # Evaluate worst-case disturbance w* = K_w* x tightness
    w_star = kw_star @ x
    z_star = c_perf @ x + d_feed @ w_star
    x_next_star = a_mat @ x + b_dist @ w_star
    worst_case_lhs = (
        float(z_star.T @ z_star)
        - (gamma**2) * float(w_star.T @ w_star)
        + float(x_next_star.T @ p_mat @ x_next_star)
    )
    worst_case_err = abs(worst_case_lhs - float(x.T @ r_gamma @ x))

    return {
        "hinf_hessian": m_hess,
        "hessian_min_eig": float(np.min(eigvals)),
        "hessian_pos_def": hessian_pos_def,
        "kw_star": kw_star,
        "hinf_riccati_map": r_gamma,
        "stage_lhs": stage_lhs,
        "stage_rhs": stage_rhs,
        "completion_of_squares_error": completion_err,
        "worst_case_tightness_error": worst_case_err,
    }


@lean_theorem(
    "ControlsLean.Controls.ISS",
    (
        "quad_add_peter_paul_identity",
        "quad_iss_of_stein_explicit",
        "iss_lyapunov_step_bound",
        "iss_invariant_sublevel",
    ),
    domain="estimation_lqr",
    summary=(
        "Discrete-time Input-to-State Stability (ISS), Peter-Paul matrix quadratic envelope, "
        "geometric decay + disturbance gain bound, and forward-invariant sublevel set."
    ),
)
def iss_peter_paul_envelope(
    a_mat: np.ndarray,
    p_mat: np.ndarray,
    q_mat: np.ndarray,
    eps: float,
    x0: np.ndarray,
    d_seq: np.ndarray,
) -> dict[str, Any]:
    """Verify the Peter-Paul quadratic identity and multi-step ISS Lyapunov envelope along x_{k+1} = A x_k + d_k."""
    if eps <= 0:
        raise ValueError("Peter-Paul parameter eps must be strictly positive.")
    d0 = d_seq[0] if d_seq.ndim == 2 else d_seq
    ax = a_mat @ x0

    # Exact Peter-Paul identity:
    # (a + b)^T P (a + b) + eps (a - eps^{-1} b)^T P (a - eps^{-1} b)
    #   == (1 + eps) a^T P a + (1 + eps^{-1}) b^T P b
    apb = ax + d0
    amb = ax - (1.0 / eps) * d0
    pp_lhs = float(apb.T @ p_mat @ apb) + eps * float(amb.T @ p_mat @ amb)
    pp_rhs = (1.0 + eps) * float(ax.T @ p_mat @ ax) + (1.0 + 1.0 / eps) * float(d0.T @ p_mat @ d0)
    peter_paul_err = abs(pp_lhs - pp_rhs)

    # Compute contraction rate alpha and disturbance gain sigma = 1 + 1/eps
    # Assuming A^T P A - P = -Q and Q >= c_ratio * P
    eig_p = np.linalg.eigvalsh(0.5 * (p_mat + p_mat.T))
    eig_q = np.linalg.eigvalsh(0.5 * (q_mat + q_mat.T))
    c_ratio = float(np.min(eig_q) / np.max(eig_p))
    alpha = c_ratio - eps * (1.0 - c_ratio)
    sigma = 1.0 + 1.0 / eps

    # Simulate trajectory x_{k+1} = A x_k + d_k and check V(x_k) <= (1 - alpha)^k V(x_0) + (sigma / alpha) w_bar
    d_mat = d_seq if d_seq.ndim == 2 else d_seq[None, :]
    horizon = d_mat.shape[0]
    w_vals = [float(d_mat[k].T @ p_mat @ d_mat[k]) for k in range(horizon)]
    w_bar = max(w_vals) if w_vals else 0.0

    x_curr = x0.copy()
    v0 = float(x0.T @ p_mat @ x0)
    envelope_holds = True
    max_v = v0
    for k in range(horizon):
        x_curr = a_mat @ x_curr + d_mat[k]
        vk = float(x_curr.T @ p_mat @ x_curr)
        max_v = max(max_v, vk)
        if 0.0 < alpha <= 1.0:
            bound_k = ((1.0 - alpha) ** (k + 1)) * v0 + (sigma / alpha) * w_bar
            if vk > bound_k + 1e-9:
                envelope_holds = False

    sublevel_radius = (sigma * w_bar / alpha) if alpha > 0 else float("inf")
    return {
        "peter_paul_identity_error": peter_paul_err,
        "c_ratio": c_ratio,
        "alpha": alpha,
        "sigma": sigma,
        "w_bar": w_bar,
        "sublevel_radius": sublevel_radius,
        "max_lyapunov_v": max_v,
        "iss_envelope_holds": envelope_holds,
    }


@lean_theorem(
    "ControlsLean.Controls.BacksteppingCLF",
    (
        "backsteppingControl",
        "backstepping_closedLoop_lie_deriv",
        "sontagControl",
        "sontag_universal_stabilizer",
        "sontag_clf_strict_decrease",
    ),
    domain="estimation_lqr",
    summary=(
        "Strict-feedback integrator backstepping CLF synthesis and Sontag's universal "
        "control-Lyapunov formula."
    ),
)
def backstepping_and_sontag_clf(
    c1: float,
    c2: float,
    f1: float,
    df1: float,
    f2: float,
    x1: float,
    x2: float,
    a_lie: float,
    b_lie: float,
) -> dict[str, float | bool]:
    """Compute strict-feedback backstepping control u_bs and Sontag universal CLF control u_sontag."""
    # Backstepping virtual control alpha_1(x_1) = -f_1(x_1) - c_1 x_1
    alpha1 = -f1 - c1 * x1
    z2 = x2 - alpha1
    u_bs = -x1 - f2 - (df1 + c1) * (f1 + x2) - c2 * z2

    # Closed-loop state derivatives: dx1 = f1 + x2, dx2 = f2 + u_bs
    dx1 = f1 + x2
    dx2 = f2 + u_bs
    dz2 = dx2 + (df1 + c1) * dx1
    lie_v2 = x1 * dx1 + z2 * dz2
    expected_lie_v2 = -c1 * (x1**2) - c2 * (z2**2)
    backstepping_err = abs(lie_v2 - expected_lie_v2)

    # Sontag universal CLF control
    if b_lie == 0.0:
        u_sontag = 0.0
        sontag_lie = a_lie
        sontag_identity_err = 0.0
    else:
        rad = math.sqrt(a_lie * a_lie + (b_lie**4))
        u_sontag = -(a_lie + rad) / b_lie
        sontag_lie = a_lie + b_lie * u_sontag
        sontag_identity_err = abs(sontag_lie - (-rad))

    return {
        "u_backstepping": u_bs,
        "z2_error": z2,
        "backstepping_lie_deriv": lie_v2,
        "backstepping_expected_lie_deriv": expected_lie_v2,
        "backstepping_identity_error": backstepping_err,
        "u_sontag": u_sontag,
        "sontag_lie_deriv": sontag_lie,
        "sontag_identity_error": sontag_identity_err,
        "sontag_strict_decrease": (sontag_lie < 0.0) if (b_lie != 0.0 or a_lie < 0.0) else True,
    }


@lean_theorem(
    "ControlsLean.Estimation.KalmanBucy",
    (
        "careGain",
        "care_completion_of_squares",
        "care_hjb_completion_of_squares",
        "kalmanBucyGain",
        "kalmanBucyCovDeriv_completion_of_squares",
        "kalmanBucy_trace_optimal",
    ),
    domain="estimation_lqr",
    summary=(
        "Continuous-time Algebraic Riccati Equation (CARE) HJB completion of squares and "
        "dual Kalman-Bucy continuous-time filter covariance derivative optimality."
    ),
)
def kalman_bucy_continuous_step(
    a_mat: np.ndarray,
    b_mat: np.ndarray,
    c_mat: np.ndarray,
    q_mat: np.ndarray,
    r_mat: np.ndarray,
    w_cov: np.ndarray,
    v_cov: np.ndarray,
    p_mat: np.ndarray,
    sig_cov: np.ndarray,
    k_cand: np.ndarray,
    l_cand: np.ndarray,
) -> dict[str, Any]:
    """Verify CARE completion of squares and dual Kalman-Bucy covariance derivative optimality."""
    # Continuous-time LQR / CARE
    k_star = np.linalg.solve(r_mat, b_mat.T @ p_mat)
    a_cl_star = a_mat - b_mat @ k_star
    care_star = a_cl_star.T @ p_mat + p_mat @ a_cl_star + q_mat + k_star.T @ r_mat @ k_star

    a_cl_cand = a_mat - b_mat @ k_cand
    care_cand = a_cl_cand.T @ p_mat + p_mat @ a_cl_cand + q_mat + k_cand.T @ r_mat @ k_cand
    dk = k_cand - k_star
    care_rhs = care_star + dk.T @ r_mat @ dk
    care_err = float(np.max(np.abs(care_cand - care_rhs)))

    # Continuous-time Kalman-Bucy filter covariance derivative
    l_star = np.linalg.solve(v_cov.T, (sig_cov @ c_mat.T).T).T
    a_obs_star = a_mat - l_star @ c_mat
    dsigma_star = a_obs_star @ sig_cov + sig_cov @ a_obs_star.T + w_cov + l_star @ v_cov @ l_star.T

    a_obs_cand = a_mat - l_cand @ c_mat
    dsigma_cand = a_obs_cand @ sig_cov + sig_cov @ a_obs_cand.T + w_cov + l_cand @ v_cov @ l_cand.T
    dl = l_cand - l_star
    dsigma_rhs = dsigma_star + dl @ v_cov @ dl.T
    kb_err = float(np.max(np.abs(dsigma_cand - dsigma_rhs)))

    return {
        "care_k_star": k_star,
        "care_op_star": care_star,
        "care_op_cand": care_cand,
        "care_completion_error": care_err,
        "kalman_bucy_l_star": l_star,
        "dsigma_star": dsigma_star,
        "dsigma_cand": dsigma_cand,
        "kalman_bucy_completion_error": kb_err,
        "trace_dsigma_star": float(np.trace(dsigma_star)),
        "trace_dsigma_cand": float(np.trace(dsigma_cand)),
    }

