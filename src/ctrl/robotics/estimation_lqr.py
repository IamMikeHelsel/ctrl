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
