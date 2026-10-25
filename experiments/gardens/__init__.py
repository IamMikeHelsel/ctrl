"""Experimental Gardens for Novel Math in Plain Sight (Controls, Vision, Reconciliation, Orchestration)."""

from __future__ import annotations

from .garden_control_orchestration import (
    AtomicTrajectoryCommitGuard,
    cbf_blend_command,
    multi_rate_cascade_envelope,
    orchestrated_command,
    pseudo_huber_loss_and_bounds,
    run_garden_control_orchestration,
    verify_orchestrator_invariants,
)
from .garden_discovery_engine import (
    certify_ldl_posdef_rational,
    mine_and_verify_plain_sight_identities,
    monomial_to_bernstein_coeffs,
    run_garden_discovery_engine,
)
from .garden_error_reconciliation import (
    precision_weighted_reconciliation,
    reconcile_and_isolate_faults,
    run_garden_error_reconciliation,
    staleness_precision_weight,
)
from .garden_stopping_going import (
    SplitAgeStoppingContract,
    actuator_transient_lag_overrun,
    decoupled_lorentz_barrier,
    exact_delay_reduction_saving,
    exact_double_count_waste,
    exact_speed_error_reduction_saving,
    naive_box_clip,
    naive_double_counted_stopping_distance,
    propagated_split_age_stopping_distance,
    radial_lorentz_kamm_project,
    raw_capture_stopping_distance,
    run_garden_stopping_going,
    softplus_derated_headroom,
    stop_go_hysteresis_band,
)
from .garden_vision_perception import (
    certify_tls_perception_duality,
    lamzouri_gram_excitation_gate,
    motion_compensated_epipolar_residual,
    run_garden_vision_perception,
    triangulate_motion_cheirality_margin,
)

__all__ = [
    "AtomicTrajectoryCommitGuard",
    "SplitAgeStoppingContract",
    "actuator_transient_lag_overrun",
    "cbf_blend_command",
    "certify_ldl_posdef_rational",
    "certify_tls_perception_duality",
    "decoupled_lorentz_barrier",
    "exact_delay_reduction_saving",
    "exact_double_count_waste",
    "exact_speed_error_reduction_saving",
    "lamzouri_gram_excitation_gate",
    "mine_and_verify_plain_sight_identities",
    "monomial_to_bernstein_coeffs",
    "motion_compensated_epipolar_residual",
    "multi_rate_cascade_envelope",
    "naive_box_clip",
    "naive_double_counted_stopping_distance",
    "orchestrated_command",
    "precision_weighted_reconciliation",
    "propagated_split_age_stopping_distance",
    "pseudo_huber_loss_and_bounds",
    "radial_lorentz_kamm_project",
    "raw_capture_stopping_distance",
    "reconcile_and_isolate_faults",
    "run_garden_control_orchestration",
    "run_garden_discovery_engine",
    "run_garden_error_reconciliation",
    "run_garden_stopping_going",
    "run_garden_vision_perception",
    "softplus_derated_headroom",
    "staleness_precision_weight",
    "stop_go_hysteresis_band",
    "triangulate_motion_cheirality_margin",
    "verify_orchestrator_invariants",
]
