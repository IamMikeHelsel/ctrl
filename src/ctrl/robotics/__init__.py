"""ctrl.robotics: Machine-checked Lean 4 robotics, control, estimation, and vision library.

Provides dual-mode (NumPy float64 + exact-Q Fraction) implementations of every theorem
proved in the 53-module ``lean/Robotics`` Lake library (``Research``, ``ControlsLean``,
and ``RoboLean``), together with deterministic C99 / IEC 61131-3 codegen, closed-loop
MuJoCo physics benchmarks, and automated ``@lean_theorem`` spec-manifest auditing.
"""

from __future__ import annotations

from ctrl.robotics import (
    codegen,
    contact_cbf,
    estimation_lqr,
    kinematics_ik,
    mujoco_benchmarks,
    registry,
    trajectories,
    vision_se3,
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
    dare_bellman_completion_of_squares,
    joseph_kalman_update,
    kalata_alpha_beta_gains,
    luenberger_separation_step,
    mpc_warm_start_cost_descent,
)
from ctrl.robotics.kinematics_ik import (
    centripetal_accel,
    euler_accel,
    max_retained_events,
    minimal_intervention_ik,
    response_time_analysis,
    rotational_transport_sq_norm,
    two_link_fk_and_jacobian,
    verify_pythagorean_ik_optimality,
    world_frame_accel,
)
from ctrl.robotics.mujoco_benchmarks import (
    run_all_mujoco_benchmarks,
    run_arm6dof_septic_energy_benchmark,
    run_quadruped_zmp_cbf_benchmark,
    run_se3_visual_servoing_benchmark,
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

__all__ = [
    "LEAN_THEOREM_REGISTRY",
    "CentroidalQuadParams",
    "LeanBinding",
    "centripetal_accel",
    "codegen",
    "compile_and_verify_c99_kernels",
    "contact_cbf",
    "dare_bellman_completion_of_squares",
    "directional_cbf",
    "electromechanical_energy",
    "emit_c99_and_iec61131",
    "estimation_lqr",
    "euler_accel",
    "filter_faugeras_chirality_branches",
    "gram_homography_vec",
    "hbvs_vs_ibvs_depth_ratio",
    "in_lorentz_cone",
    "joseph_kalman_update",
    "kalata_alpha_beta_gains",
    "kinematics_ik",
    "lean_theorem",
    "lorentz_cbf_safety_filter",
    "luenberger_separation_step",
    "max_retained_events",
    "minimal_intervention_ik",
    "mpc_warm_start_cost_descent",
    "mujoco_benchmarks",
    "optimal_septic_eta",
    "quad_contact_forces",
    "quad_normal_force",
    "registry",
    "response_time_analysis",
    "rotational_transport_sq_norm",
    "run_all_mujoco_benchmarks",
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
    "timewarp_derivatives",
    "trajectories",
    "triangulate_two_view_rays",
    "two_link_fk_and_jacobian",
    "verify_homography_singular_sandwich",
    "verify_lean_bindings",
    "verify_pythagorean_ik_optimality",
    "verify_quad_wrench_balance",
    "vision_se3",
    "world_frame_accel",
]
