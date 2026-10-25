/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Vision.PerceptionReconciliation
import ControlsLean.Controls.ControlOrchestration

/-!
# Vision & Perception Hardening + Control Orchestration Re-Export & Axiom Audit

Re-exports and audits the machine-checked theorems of
`ControlsLean.Vision.PerceptionReconciliation` and `ControlsLean.Controls.ControlOrchestration`
inside the `Research` experimental garden for `/Users/mike/Dev/ctrl/lean`.
-/

namespace Research.VisionPerceptionHardening

#print axioms ControlsLean.Controls.transient_lag_clearance_saving
#print axioms ControlsLean.Controls.stopping_go_hysteresis_gap_pos
#print axioms ControlsLean.Controls.go_admissible_iff_headway_gt_stop_plus_hysteresis
#print axioms ControlsLean.Controls.hasDerivAt_decoupledConeBarrier
#print axioms ControlsLean.Controls.decoupled_cone_barrier_deriv_eq
#print axioms ControlsLean.Controls.decoupled_cone_barrier_no_tangential_leakage
#print axioms ControlsLean.Controls.headroom_derated_stopping_margin
#print axioms ControlsLean.Controls.reconciliation_quadratic_completion
#print axioms ControlsLean.Controls.reconciliation_disagreement_eq_pairwise
#print axioms ControlsLean.Controls.reconciliation_variance_pairwise_identity
#print axioms ControlsLean.Controls.reconciliation_fault_isolation_bound
#print axioms ControlsLean.Controls.staleness_inflated_precision_mono
#print axioms ControlsLean.Controls.orchestrator_convex_hull_invariance
#print axioms ControlsLean.Controls.orchestrator_safety_margin_monotonicity
#print axioms ControlsLean.Controls.multi_rate_cascade_iss_bound
#print axioms ControlsLean.Controls.pseudo_huber_bounds_and_lipschitz
#print axioms ControlsLean.Vision.epipolar_motion_shift_identity
#print axioms ControlsLean.Vision.epipolar_motion_bias_identity
#print axioms ControlsLean.Vision.epipolar_motion_bias_bound
#print axioms ControlsLean.Vision.cheirality_sign_invariant_of_motion_margin
#print axioms ControlsLean.Vision.tls_dual_weight_identity
#print axioms ControlsLean.Vision.tls_optimal_weight_one_of_inlier
#print axioms ControlsLean.Vision.tls_optimal_weight_zero_of_outlier
#print axioms ControlsLean.Vision.tls_objective_le_unweighted
#print axioms ControlsLean.Vision.gram2_trace_sq_sub_trace_sq_eq_two_det
#print axioms ControlsLean.Vision.gram2_trace_sq_bounds
#print axioms ControlsLean.Vision.gram2_det_pos_of_effRank_gt_one
#print axioms ControlsLean.Vision.gram2_posDef_of_trace_pos_effRank_gt_one

end Research.VisionPerceptionHardening
