"""ctrl.robotics: Machine-checked Lean 4 robotics, control, estimation, and vision library.

Provides dual-mode (NumPy float64 + exact-Q Fraction) implementations of every theorem
proved in the unified ``lean/Robotics`` Lake library (``Research``, ``ControlsLean``,
and ``RoboLean``), together with deterministic C99 / IEC 61131-3 codegen, exact rational
safety-filter certificates, closed-loop MuJoCo physics benchmarks (lazy-loaded on demand),
and automated ``@lean_theorem`` spec-manifest auditing.
"""

from __future__ import annotations

import importlib
from typing import Any

from ctrl.robotics import (
    certified_guard,
    codegen,
    contact_cbf,
    estimation_lqr,
    kinematics_ik,
    orchestration_reconciliation,
    registry,
    trajectories,
    vision_se3,
)
from ctrl.robotics.orchestration_reconciliation import (
    decoupled_cone_barrier_and_deriv,
    gram2_effective_rank_gate,
    motion_compensated_epipolar_and_cheirality,
    orchestrate_multi_rate_control,
    precision_reconcile_sensors,
    stop_go_hysteresis_envelope,
    tls_primal_dual_certificate,
    transient_lag_stopping_envelope,
)
from ctrl.robotics.certified_guard import (
    CertifiedGuardResult,
    CertifiedGuardStatus,
    certified_plc_box_guard,
    certify_osqp_safety_filter,
    compute_four_support_interval,
    verify_farkas_box_certificate,
)
from ctrl.robotics.codegen import compile_and_verify_c99_kernels, emit_c99_and_iec61131
from ctrl.robotics.contact_cbf import (
    CentroidalQuadParams,
    directional_cbf,
    in_lorentz_cone,
    lorentz_cbf_safety_filter,
    quad_contact_forces,
    quad_normal_force,
    safe_decel_max,
    verify_quad_wrench_balance,
)
from ctrl.robotics.estimation_lqr import (
    backstepping_and_sontag_clf,
    dare_bellman_completion_of_squares,
    dare_detectable_return_difference_margin,
    hinf_bounded_real_step,
    iss_peter_paul_envelope,
    joseph_kalman_update,
    kalata_alpha_beta_gains,
    kalman_bucy_continuous_step,
    luenberger_separation_step,
    mpc_warm_start_cost_descent,
    pomdp_bayes_belief_update,
    pomdp_pwlc_bellman_backup,
)
from ctrl.robotics.kinematics_ik import (
    centripetal_accel,
    euler_accel,
    max_retained_events,
    minimal_intervention_ik,
    response_time_analysis,
    rotational_transport_sq_norm,
    slotine_li_adaptive_update,
    slotine_li_control_torque,
    slotine_li_sliding_error,
    two_link_fk_and_jacobian,
    verify_pythagorean_ik_optimality,
    world_frame_accel,
)
from ctrl.robotics.registry import (
    LEAN_THEOREM_REGISTRY,
    LeanBinding,
    lean_theorem,
    verify_lean_bindings,
)
from ctrl.robotics.trajectories import (
    electromechanical_energy,
    optimal_septic_eta,
    septic_a,
    septic_accel_integral,
    septic_j,
    septic_jerk_integral,
    septic_q,
    septic_v,
    septic_velocity_integral,
    timewarp_derivatives,
)
from ctrl.robotics.vision_se3 import (
    filter_faugeras_chirality_branches,
    gram_homography_vec,
    hbvs_vs_ibvs_depth_ratio,
    se3_depth_derivative,
    triangulate_two_view_rays,
    verify_homography_singular_sandwich,
)

_MUJOCO_EXPORTS = {
    "mujoco_benchmarks",
    "run_all_mujoco_benchmarks",
    "run_arm6dof_disturbance_iss_hinf_benchmark",
    "run_arm6dof_septic_energy_benchmark",
    "run_quadruped_zmp_cbf_benchmark",
    "run_se3_visual_servoing_benchmark",
}


def __getattr__(name: str) -> Any:
    """Lazy-load ``mujoco_benchmarks`` on demand so ``import ctrl.robotics`` avoids eager MuJoCo import."""
    if name in _MUJOCO_EXPORTS:
        mod = importlib.import_module("ctrl.robotics.mujoco_benchmarks")
        globals()["mujoco_benchmarks"] = mod
        for attr in _MUJOCO_EXPORTS - {"mujoco_benchmarks"}:
            globals()[attr] = getattr(mod, attr)
        return globals()[name]
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


__all__ = [
    "LEAN_THEOREM_REGISTRY",
    "CentroidalQuadParams",
    "CertifiedGuardResult",
    "CertifiedGuardStatus",
    "LeanBinding",
    "backstepping_and_sontag_clf",
    "centripetal_accel",
    "certified_guard",
    "certified_plc_box_guard",
    "certify_osqp_safety_filter",
    "codegen",
    "compile_and_verify_c99_kernels",
    "compute_four_support_interval",
    "contact_cbf",
    "dare_bellman_completion_of_squares",
    "dare_detectable_return_difference_margin",
    "decoupled_cone_barrier_and_deriv",
    "directional_cbf",
    "electromechanical_energy",
    "emit_c99_and_iec61131",
    "estimation_lqr",
    "euler_accel",
    "filter_faugeras_chirality_branches",
    "gram2_effective_rank_gate",
    "gram_homography_vec",
    "hbvs_vs_ibvs_depth_ratio",
    "hinf_bounded_real_step",
    "in_lorentz_cone",
    "iss_peter_paul_envelope",
    "joseph_kalman_update",
    "kalata_alpha_beta_gains",
    "kalman_bucy_continuous_step",
    "kinematics_ik",
    "lean_theorem",
    "lorentz_cbf_safety_filter",
    "luenberger_separation_step",
    "max_retained_events",
    "minimal_intervention_ik",
    "motion_compensated_epipolar_and_cheirality",
    "mpc_warm_start_cost_descent",
    "mujoco_benchmarks",
    "optimal_septic_eta",
    "orchestrate_multi_rate_control",
    "orchestration_reconciliation",
    "pomdp_bayes_belief_update",
    "pomdp_pwlc_bellman_backup",
    "precision_reconcile_sensors",
    "quad_contact_forces",
    "quad_normal_force",
    "registry",
    "response_time_analysis",
    "rotational_transport_sq_norm",
    "run_all_mujoco_benchmarks",
    "run_arm6dof_disturbance_iss_hinf_benchmark",
    "run_arm6dof_septic_energy_benchmark",
    "run_quadruped_zmp_cbf_benchmark",
    "run_se3_visual_servoing_benchmark",
    "safe_decel_max",
    "se3_depth_derivative",
    "septic_a",
    "septic_accel_integral",
    "septic_j",
    "septic_jerk_integral",
    "septic_q",
    "septic_v",
    "septic_velocity_integral",
    "slotine_li_adaptive_update",
    "slotine_li_control_torque",
    "slotine_li_sliding_error",
    "stop_go_hysteresis_envelope",
    "timewarp_derivatives",
    "tls_primal_dual_certificate",
    "trajectories",
    "transient_lag_stopping_envelope",
    "triangulate_two_view_rays",
    "two_link_fk_and_jacobian",
    "verify_farkas_box_certificate",
    "verify_homography_singular_sandwich",
    "verify_lean_bindings",
    "verify_pythagorean_ik_optimality",
    "verify_quad_wrench_balance",
    "vision_se3",
    "world_frame_accel",
]
