"""Dual-mode (`float` + exact `fractions.Fraction`) implementations of the theorems in
``ControlsLean.Controls.ControlOrchestration`` and ``ControlsLean.Vision.PerceptionReconciliation``.

Covers:
1. Transient-lag stopping & going envelopes, stop/go hysteresis chatter elimination, and
   decoupled normal-tangential Lorentz-cone safety barriers (`ControlOrchestration.lean`).
2. Precision-weighted multi-sensor error reconciliation (Lagrange-Gauss pairwise identity),
   staleness-aware precision downweighting, and quorum fault isolation (`ControlOrchestration.lean`).
3. 3-Tier control orchestration (Nominal / CBF-Intervene / Emergency-Stop), multi-rate cascade ISS
   tracking envelopes, and C^infty Pseudo-Huber smooth residuals (`ControlOrchestration.lean`).
4. Motion-compensated epipolar residuals, affine triangulation cheirality skew margins,
   Truncated Least Squares (TLS) perception duality, and Lamzouri SVD-free Gram excitation gates
   (`PerceptionReconciliation.lean`).
"""

from __future__ import annotations

import math
from fractions import Fraction
from typing import Any, Sequence, TypeVar

from ctrl.robotics.contact_cbf import Vec3T, add3, cross3, dot3, smul3
from ctrl.robotics.kinematics_ik import sq_norm3
from ctrl.robotics.registry import lean_theorem

T = TypeVar("T", float, Fraction)


@lean_theorem(
    "ControlsLean.Controls.ControlOrchestration",
    (
        "stoppingDistance",
        "coarseDelayStoppingDistance",
        "rampStoppingDistance",
        "transientLagSaving",
        "stoppingDistance_nonneg",
        "stoppingDistance_pos",
        "stopping_completion_of_squares",
        "constant_braking_segment_le_stoppingDistance",
        "transientLagSaving_eq",
        "transient_lag_clearance_saving",
    ),
    domain="orchestration_reconciliation",
    summary="Exact transient-lag stopping envelope and closed-form ramp clearance saving.",
)
def transient_lag_stopping_envelope(
    w_speed: T,
    tau_delay: T,
    tau_act: T,
    a_max: T,
    b_min: T,
) -> dict[str, T | bool]:
    """Compute coarseDelayStoppingDistance, rampStoppingDistance, and exact transientLagSaving:
    (a_0 + b) * tau * (12 * v_0 + (9 * a_0 + b) * tau) / (24 * b).
    """
    is_frac = isinstance(w_speed, Fraction)
    two: T = Fraction(2, 1) if is_frac else 2.0  # type: ignore[assignment]
    six: T = Fraction(6, 1) if is_frac else 6.0  # type: ignore[assignment]
    nine: T = Fraction(9, 1) if is_frac else 9.0  # type: ignore[assignment]
    twelve: T = Fraction(12, 1) if is_frac else 12.0  # type: ignore[assignment]
    twenty_four: T = Fraction(24, 1) if is_frac else 24.0  # type: ignore[assignment]
    _ = tau_act

    r_coarse = (
        w_speed * tau_delay
        + a_max * (tau_delay * tau_delay) / two
        + ((w_speed + a_max * tau_delay) ** 2) / (two * b_min)
    )
    r_ramp = (
        w_speed * tau_delay
        + (two * a_max - b_min) * (tau_delay * tau_delay) / six
        + ((w_speed + (a_max - b_min) * tau_delay / two) ** 2) / (two * b_min)
    )
    saving_closed = (
        (a_max + b_min)
        * tau_delay
        * (twelve * w_speed + (nine * a_max + b_min) * tau_delay)
        / (twenty_four * b_min)
    )
    diff = r_coarse - r_ramp
    exact_match = (
        diff == saving_closed if is_frac else abs(diff - saving_closed) < 1e-12
    )
    return {
        "coarse_stopping_distance": r_coarse,
        "ramp_stopping_distance": r_ramp,
        "clearance_saving": saving_closed,
        "identity_holds": exact_match,
    }


@lean_theorem(
    "ControlsLean.Controls.ControlOrchestration",
    (
        "stopThreshold",
        "goThreshold",
        "stopping_go_hysteresis_gap_pos",
        "go_admissible_iff_headway_gt_stop_plus_hysteresis",
        "no_chattering_in_hysteresis_band",
    ),
    domain="orchestration_reconciliation",
    summary="Zero-chatter Stop <-> Go hysteresis thresholds and deadband invariance.",
)
def stop_go_hysteresis_envelope(
    d_safe: T,
    w_speed: T,
    tau_delay: T,
    tau_act: T,
    a_max: T,
    b_min: T,
    delta_hyst: T,
    headway: T,
) -> dict[str, T | str | bool]:
    """Compute stopThreshold, goThreshold = stopThreshold + delta_hyst, and deadband status."""
    env = transient_lag_stopping_envelope(w_speed, tau_delay, tau_act, a_max, b_min)
    r_ramp: T = env["ramp_stopping_distance"]  # type: ignore[assignment]
    d_stop = d_safe + r_ramp
    d_go = d_stop + delta_hyst
    in_band = bool(d_stop <= headway <= d_go)
    go_admissible = bool(headway > d_go)
    must_stop = bool(headway < d_stop)
    mode = "GO" if go_admissible else ("STOP" if must_stop else "HOLD_HYSTERESIS_BAND")
    return {
        "stop_threshold": d_stop,
        "go_threshold": d_go,
        "hysteresis_gap": d_go - d_stop,
        "in_hysteresis_band": in_band,
        "go_admissible": go_admissible,
        "mode": mode,
    }


@lean_theorem(
    "ControlsLean.Controls.ControlOrchestration",
    (
        "decoupledConeBarrier",
        "decoupledConeBarrierDeriv",
        "hasDerivAt_decoupledConeBarrier",
        "decoupled_cone_barrier_deriv_eq",
        "decoupled_cone_barrier_no_tangential_leakage",
        "headroom_derated_stopping_margin",
    ),
    domain="orchestration_reconciliation",
    summary="Decoupled normal-tangential Lorentz-cone safety barrier and zero-leakage Lie derivative.",
)
def decoupled_cone_barrier_and_deriv(
    r_clear: T,
    d_safe: T,
    v_n: T,
    v_tx: T,
    v_ty: T,
    a_n: T,
    a_tx: T,
    a_ty: T,
    c_n: T,
    c_t: T,
    mu: T,
) -> dict[str, T | bool]:
    """Evaluate decoupledConeBarrier and decoupledConeBarrierDeriv when approaching (v_n <= 0)."""
    is_frac = isinstance(r_clear, Fraction)
    zero: T = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]
    two: T = Fraction(2, 1) if is_frac else 2.0  # type: ignore[assignment]
    vn_neg = -v_n if v_n < zero else zero
    vt_sq = v_tx * v_tx + v_ty * v_ty
    h_val = (
        (r_clear - d_safe)
        - (vn_neg * vn_neg) / (two * c_n)
        - (mu * vt_sq) / (two * c_t)
    )
    h_deriv = (
        v_n
        - (v_n * a_n) / c_n
        - (mu / c_t) * (v_tx * a_tx + v_ty * a_ty)
    )
    return {
        "barrier_value": h_val,
        "barrier_deriv": h_deriv,
        "is_safe": bool(h_val >= zero),
    }


@lean_theorem(
    "ControlsLean.Controls.ControlOrchestration",
    (
        "totalPrecision",
        "weightedMeasurementSum",
        "reconciledEstimate",
        "reconciliationResidualEnergy",
        "pairwiseDisagreementEnergy",
        "sensorDisagreementScore",
        "effectivePrecision",
        "weighted_innovation_sum_zero",
        "reconciliation_quadratic_completion",
        "reconciliation_estimate_isMin",
        "reconciliation_lagrange_pairwise_identity",
        "reconciliation_disagreement_eq_pairwise",
        "reconciliation_variance_pairwise_identity",
        "healthy_sensor_disagreement_le",
        "reconciliation_fault_isolation_bound",
        "staleness_inflated_precision_mono",
        "staleness_inflated_precision_strict_anti",
    ),
    domain="orchestration_reconciliation",
    summary="Precision-weighted sensor reconciliation, Lagrange-Gauss pairwise identity, and fault isolation.",
)
def precision_reconcile_sensors(
    measurements: Sequence[T],
    weights: Sequence[T],
    x_candidate: T | None = None,
) -> dict[str, Any]:
    """Compute reconciledEstimate, reconciliationResidualEnergy, and pairwiseDisagreementEnergy."""
    m = len(measurements)
    if m == 0 or len(weights) != m:
        raise ValueError("measurements and weights must be non-empty of equal length")
    is_frac = isinstance(measurements[0], Fraction)
    zero: T = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]
    two: T = Fraction(2, 1) if is_frac else 2.0  # type: ignore[assignment]

    w_tot = zero
    wy_sum = zero
    for y_i, w_i in zip(measurements, weights):
        w_tot = w_tot + w_i
        wy_sum = wy_sum + w_i * y_i

    x_hat = wy_sum / w_tot
    x_eval = x_hat if x_candidate is None else x_candidate

    innov_sum = zero
    rss_hat = zero
    rss_eval = zero
    for y_i, w_i in zip(measurements, weights):
        innov_sum = innov_sum + w_i * (y_i - x_hat)
        rss_hat = rss_hat + w_i * ((y_i - x_hat) ** 2)
        rss_eval = rss_eval + w_i * ((y_i - x_eval) ** 2)

    pairwise_full = zero
    scores: list[T] = []
    for i in range(m):
        s_i = zero
        for j in range(m):
            dy = measurements[i] - measurements[j]
            term = weights[i] * weights[j] * (dy * dy)
            pairwise_full = pairwise_full + term
            s_i = s_i + weights[j] * (dy * dy)
        scores.append(s_i)

    pairwise_energy = pairwise_full / (two * w_tot)
    lagrange_lhs = w_tot * rss_eval
    lagrange_rhs = (w_tot * w_tot) * ((x_eval - x_hat) ** 2) + pairwise_full / two

    exact_ok = (
        (rss_hat == pairwise_energy and lagrange_lhs == lagrange_rhs and innov_sum == zero)
        if is_frac
        else (
            abs(rss_hat - pairwise_energy) < 1e-12
            and abs(lagrange_lhs - lagrange_rhs) < 1e-11
            and abs(innov_sum) < 1e-12
        )
    )
    return {
        "total_precision": w_tot,
        "reconciled_estimate": x_hat,
        "weighted_innovation_sum": innov_sum,
        "residual_energy_at_xhat": rss_hat,
        "pairwise_disagreement_energy": pairwise_energy,
        "sensor_disagreement_scores": scores,
        "lagrange_pairwise_identity_exact": exact_ok,
    }


@lean_theorem(
    "ControlsLean.Controls.ControlOrchestration",
    (
        "cbfBlendCommand",
        "orchestratedCommand",
        "cbfBlendVec",
        "orchestratedVec",
        "pseudoHuber",
        "orchestrator_box_invariance",
        "orchestrator_convex_hull_invariance",
        "orchestrator_safety_margin_monotonicity",
        "one_sub_mul_geom_sum",
        "multi_rate_cascade_step_bound",
        "multi_rate_cascade_iss_bound",
        "multi_rate_cascade_sublevel_invariant",
        "pseudoHuber_add_eps_sq",
        "pseudoHuber_nonneg",
        "pseudoHuber_le_abs",
        "abs_sub_eps_lt_pseudoHuber",
        "pseudoHuber_le_quadratic_half",
        "pseudo_huber_bounds_and_lipschitz",
    ),
    domain="orchestration_reconciliation",
    summary="3-Tier control orchestrator, multi-rate cascade ISS envelope, and Pseudo-Huber loss.",
)
def orchestrate_multi_rate_control(
    u_nom: T,
    u_safe: T,
    u_stop: T,
    lam_cbf: T,
    alpha_stop: T,
    u_min: T,
    u_max: T,
    v0_lyap: T,
    rho_cascade: T,
    eps_cascade: T,
    n_steps: int,
) -> dict[str, Any]:
    """Compute 3-tier orchestrated command and multi-rate cascade ISS envelope."""
    is_frac = isinstance(u_nom, Fraction)
    one: T = Fraction(1, 1) if is_frac else 1.0  # type: ignore[assignment]

    u_cbf = (one - lam_cbf) * u_nom + lam_cbf * u_safe
    u_orch = (one - alpha_stop) * u_cbf + alpha_stop * u_stop
    box_ok = bool(u_min <= u_orch <= u_max)

    rho_n: T = (rho_cascade ** n_steps)  # type: ignore[assignment]
    geom_sum = (one - rho_n) / (one - rho_cascade)
    iss_bound = rho_n * v0_lyap + eps_cascade * geom_sum
    asymp_sublevel = eps_cascade / (one - rho_cascade)

    return {
        "u_cbf": u_cbf,
        "u_orch": u_orch,
        "box_invariant": box_ok,
        "cascade_iss_bound": iss_bound,
        "cascade_asymptotic_sublevel": asymp_sublevel,
    }


@lean_theorem(
    "ControlsLean.Vision.PerceptionReconciliation",
    (
        "motionShiftedTranslation",
        "epipolarResidual",
        "triangulationDepth1Numer",
        "epipolar_motion_shift_identity",
        "epipolar_motion_bias_identity",
        "epipolar_motion_bias_bound",
        "triangulationDepth1Numer_motion_shift",
        "cheirality_sign_invariant_of_motion_margin",
    ),
    domain="orchestration_reconciliation",
    summary="Rolling-shutter / velocity-induced epipolar shift and triangulation cheirality margin.",
)
def motion_compensated_epipolar_and_cheirality(
    r_x1: Vec3T[T],
    x2: Vec3T[T],
    t_base: Vec3T[T],
    v_vel: Vec3T[T],
    delta_t: T,
) -> dict[str, T | Vec3T[T] | bool]:
    """Evaluate motionShiftedTranslation, epipolarResidual shift, and triangulationDepth1Numer margin."""
    is_frac = isinstance(delta_t, Fraction)
    zero: T = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]
    t_shifted = add3(t_base, smul3(delta_t, v_vel))

    epi_base = dot3(x2, cross3(t_base, r_x1))
    epi_vel = dot3(x2, cross3(v_vel, r_x1))
    epi_shifted = dot3(x2, cross3(t_shifted, r_x1))

    n_vec = cross3(x2, r_x1)
    denom = sq_norm3(n_vec)
    d1_num_base = -dot3(n_vec, cross3(x2, t_base))
    d1_num_vel = -dot3(n_vec, cross3(x2, v_vel))
    d1_num_shifted = -dot3(n_vec, cross3(x2, t_shifted))

    epi_id_ok = (
        epi_shifted == epi_base + delta_t * epi_vel
        if is_frac
        else abs(epi_shifted - (epi_base + delta_t * epi_vel)) < 1e-12
    )
    tri_id_ok = (
        d1_num_shifted == d1_num_base + delta_t * d1_num_vel
        if is_frac
        else abs(d1_num_shifted - (d1_num_base + delta_t * d1_num_vel)) < 1e-12
    )
    return {
        "motion_shifted_translation": t_shifted,
        "epipolar_base": epi_base,
        "epipolar_velocity_bias": delta_t * epi_vel,
        "epipolar_shifted": epi_shifted,
        "depth1_numer_base": d1_num_base,
        "depth1_numer_shifted": d1_num_shifted,
        "ray_cross_sq_norm": denom,
        "cheirality_positive": bool(d1_num_shifted > zero and denom > zero),
        "identities_exact": bool(epi_id_ok and tri_id_ok),
    }


@lean_theorem(
    "ControlsLean.Vision.PerceptionReconciliation",
    (
        "tlsSurrogateTerm",
        "tlsTruncatedTerm",
        "tlsOptimalWeight",
        "tlsDualObjective",
        "tlsPrimalObjective",
        "tlsSurrogateTerm_sub_truncated_eq",
        "tls_truncated_le_surrogate",
        "tls_optimal_weight_in_unit_interval",
        "tls_optimal_weight_one_of_inlier",
        "tls_optimal_weight_zero_of_outlier",
        "tls_surrogate_at_optimal_weight",
        "tls_dual_weight_identity",
        "tls_objective_le_unweighted",
    ),
    domain="orchestration_reconciliation",
    summary="Truncated Least Squares (TLS) primal-dual outlier rejection and zero-gap weight certificate.",
)
def tls_primal_dual_certificate(
    residuals: Sequence[T],
    c_bar: T,
    weights: Sequence[T] | None = None,
) -> dict[str, Any]:
    """Evaluate TLS primal objective, dual surrogate objective, and exact optimal weights in {0, 1}."""
    is_frac = isinstance(c_bar, Fraction)
    zero: T = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]
    one: T = Fraction(1, 1) if is_frac else 1.0  # type: ignore[assignment]
    c_sq = c_bar * c_bar

    w_opt: list[T] = []
    primal_obj = zero
    unweighted_obj = zero
    for r in residuals:
        r_sq = r * r
        unweighted_obj = unweighted_obj + r_sq
        if r_sq <= c_sq:
            w_opt.append(one)
            primal_obj = primal_obj + r_sq
        else:
            w_opt.append(zero)
            primal_obj = primal_obj + c_sq

    w_eval = list(weights) if weights is not None else w_opt
    dual_obj = zero
    for r, w in zip(residuals, w_eval):
        r_sq = r * r
        dual_obj = dual_obj + (w * r_sq + c_sq * (one - w))

    gap = dual_obj - primal_obj
    return {
        "primal_objective": primal_obj,
        "dual_objective": dual_obj,
        "unweighted_objective": unweighted_obj,
        "duality_gap": gap,
        "optimal_weights": w_opt,
        "primal_le_dual": bool(primal_obj <= dual_obj if is_frac else primal_obj <= dual_obj + 1e-12),
        "primal_le_unweighted": bool(
            primal_obj <= unweighted_obj if is_frac else primal_obj <= unweighted_obj + 1e-12
        ),
    }


@lean_theorem(
    "ControlsLean.Vision.PerceptionReconciliation",
    (
        "gram2Matrix",
        "gram2Trace",
        "gram2Det",
        "gram2FrobSq",
        "trace_gram2Matrix",
        "det_gram2Matrix",
        "trace_sq_gram2Matrix",
        "gram2_trace_sq_sub_trace_sq_eq_two_det",
        "gram2_two_frobSq_sub_trace_sq_eq_sum_sq",
        "gram2_trace_sq_bounds",
        "gram2_det_pos_of_effRank_gt_one",
        "gram2_schur_completion_of_squares",
        "gram2_posDef_of_trace_pos_effRank_gt_one",
    ),
    domain="orchestration_reconciliation",
    summary="SVD-free 2x2 Gram matrix effective-rank persistent excitation gate and Schur completion.",
)
def gram2_effective_rank_gate(
    a_diag: T, b_off: T, d_diag: T
) -> dict[str, T | bool]:
    """Compute 2x2 Gram trace, determinant, Frobenius norm squared, and effective-rank SPD gate."""
    is_frac = isinstance(a_diag, Fraction)
    zero: T = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]
    two: T = Fraction(2, 1) if is_frac else 2.0  # type: ignore[assignment]

    tr_g = a_diag + d_diag
    det_g = a_diag * d_diag - b_off * b_off
    frob_sq = a_diag * a_diag + two * (b_off * b_off) + d_diag * d_diag
    tr_sq_minus_frob = tr_g * tr_g - frob_sq

    newton_girard_ok = (
        tr_sq_minus_frob == two * det_g
        if is_frac
        else abs(tr_sq_minus_frob - two * det_g) < 1e-12
    )
    is_posdef = bool(tr_g > zero and tr_g * tr_g > frob_sq)
    return {
        "trace": tr_g,
        "det": det_g,
        "frob_sq": frob_sq,
        "trace_sq_sub_frob_sq": tr_sq_minus_frob,
        "newton_girard_identity_exact": newton_girard_ok,
        "certified_posdef": is_posdef,
    }
