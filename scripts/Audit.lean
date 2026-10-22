import ControlsLean

-- Each headline theorem must depend only on propext, Classical.choice, Quot.sound.

-- Seed: Vision (Epipolar geometry)
#print axioms ControlsLean.Vision.epipolar_constraint
#print axioms ControlsLean.Vision.det_essential

-- Seed: Controls (Hurwitz-2 stability)
#print axioms ControlsLean.Controls.isHurwitz2_iff

-- Seed: Controls (Reachability & Controllability without Cayley-Hamilton)
#print axioms ControlsLean.Controls.reach_eq_reach_finrank
#print axioms ControlsLean.Controls.controllable_iff_finrank
#print axioms ControlsLean.Controls.Controllable.exists_steer
#print axioms ControlsLean.Controls.controllable_feedback

-- Seed: Controls (Discrete Lyapunov asymptotic stability)
#print axioms ControlsLean.Controls.tendsto_pow_mulVec_zero
#print axioms ControlsLean.Controls.PosDef.tendsto_pow_mulVec_zero

-- Seed: Estimation (Scalar Kalman filter & Riccati contraction)
#print axioms ControlsLean.Estimation.postVar_eq_opt_iff
#print axioms ControlsLean.Estimation.inv_postVarOpt
#print axioms ControlsLean.Estimation.riccati_fixed_unique

-- Addition 1: Vision (Planar Homography & Collineation)
#print axioms ControlsLean.Vision.lineTransform_dotProduct
#print axioms ControlsLean.Vision.det_homography_three_points
#print axioms ControlsLean.Vision.collinear_homography
#print axioms ControlsLean.Vision.plane_homography_constraint

-- Addition 2: Controls (Controllability Gramian & Minimum-Energy Steering)
#print axioms ControlsLean.Controls.term_transpose
#print axioms ControlsLean.Controls.gramian_transpose
#print axioms ControlsLean.Controls.quad_gramian_term
#print axioms ControlsLean.Controls.gramian_steer

-- Addition 3: Estimation (Sherman-Morrison-Woodbury & Information Filtering)
#print axioms ControlsLean.Estimation.woodbury_right_inv
#print axioms ControlsLean.Estimation.woodbury_left_inv
#print axioms ControlsLean.Estimation.woodbury_isInverse
#print axioms ControlsLean.Estimation.kalman_information_equivalence

-- Addition 4: Controls (State Feedback, Deadbeat Nilpotence & Hurwitz Stabilization)
#print axioms ControlsLean.Controls.closedLoop_eq
#print axioms ControlsLean.Controls.deadbeat_gain
#print axioms ControlsLean.Controls.deadbeat_nilpotent
#print axioms ControlsLean.Controls.deadbeat_trajectory_zero
#print axioms ControlsLean.Controls.hurwitz_stabilization

-- Addition 5: Tactics & Control Engineering Formalization (ControlTactics)
#print axioms ControlsLean.Tactics.posDef_iff_quad_pos
#print axioms ControlsLean.Tactics.quad_fromBlocks
#print axioms ControlsLean.Tactics.quad_transpose
#print axioms ControlsLean.Tactics.inv_parallel_sum
#print axioms ControlsLean.Tactics.riccati_lft_form
#print axioms ControlsLean.Tactics.riccati_fixed_iff_quadratic
#print axioms ControlsLean.Tactics.lyapunov_geometric_mulVec
#print axioms ControlsLean.Tactics.quad_lyapunov_geometric

-- Addition 6: Estimation (Scalar Riccati iteration convergence)
#print axioms ControlsLean.Estimation.abs_riccati_iterate_sub_le
#print axioms ControlsLean.Estimation.tendsto_riccati_iterate
#print axioms ControlsLean.Estimation.tendsto_gain_riccati_iterate

-- Addition 7: Controls (Luenberger Observers & Separation Principle)
#print axioms ControlsLean.Controls.observer_error_step
#print axioms ControlsLean.Controls.observer_error_pow
#print axioms ControlsLean.Controls.closed_loop_separation_block
#print axioms ControlsLean.Controls.closed_loop_separation_det
#print axioms ControlsLean.Controls.closed_loop_separation_charpoly

-- Integrated PR #11 (Issue #5): Controls (Jury stability test, degree 2)
#print axioms ControlsLean.Controls.isSchur2_iff
#print axioms ControlsLean.Controls.isSchur2_iff_jury

-- Integrated PR #12 (Issue #9): Vision (Eight-point algorithm: E determined up to scale)
#print axioms ControlsLean.Vision.finrank_ker_constraintMatrix
#print axioms ControlsLean.Vision.eq_smul_of_rank_eq_eight
#print axioms ControlsLean.Vision.essential_satisfies_constraints
#print axioms ControlsLean.Vision.eq_smul_essential

-- Integrated PR #14 (Issue #4): Controls (Observability as the dual of controllability)
#print axioms ControlsLean.Controls.unobs_eq_dualCoannihilator_reach
#print axioms ControlsLean.Controls.observable_iff_controllable_dual
#print axioms ControlsLean.Controls.unobs_eq_unobs_finrank
#print axioms ControlsLean.Controls.observable_iff_forall
#print axioms ControlsLean.Controls.Observable.eq_of_output_eq
#print axioms ControlsLean.Controls.observable_outputInjection

-- Integrated PR #16 (Issue #13): Vision (Two-view triangulation)
#print axioms ControlsLean.Vision.depth₁_eq
#print axioms ControlsLean.Vision.depth₂_eq
#print axioms ControlsLean.Vision.depths_unique
#print axioms ControlsLean.Vision.scene_closedForm
#print axioms ControlsLean.Vision.exists_depths_iff
#print axioms ControlsLean.Vision.cheirality

-- Integrated PR #18 (Issue #15): Controls (Discrete-time small-gain theorem)
#print axioms ControlsLean.Controls.small_gain
#print axioms ControlsLean.Controls.small_gain_bounded
#print axioms ControlsLean.Controls.HasGain.linear_zero_bias
#print axioms ControlsLean.Controls.small_gain_linear

-- Integrated PR #19 (Issue #17): Estimation (Steady-state alpha-beta filter & Kalata relation)
#print axioms ControlsLean.Estimation.AlphaBeta.riccatiMap_eq_iff
#print axioms ControlsLean.Estimation.AlphaBeta.gain_quadratic
#print axioms ControlsLean.Estimation.AlphaBeta.beta_sq_div
#print axioms ControlsLean.Estimation.AlphaBeta.kalata
#print axioms ControlsLean.Estimation.AlphaBeta.isSteadyState_of_gains
#print axioms ControlsLean.Estimation.AlphaBeta.exists_gains
#print axioms ControlsLean.Estimation.AlphaBeta.exists_steadyState

-- Integrated PR #20 (Issue #8, part 1): Controls (Companion matrix & canonical form)
#print axioms ControlsLean.Controls.charpoly_companion
#print axioms ControlsLean.Controls.companion_add_vecMulVec
#print axioms ControlsLean.Controls.charpoly_companion_feedback
#print axioms ControlsLean.Controls.exists_feedback_charpoly_eq
#print axioms ControlsLean.Controls.controllable_companion

-- Integrated PR #21 (Issue #8, part 2): Controls (General-n single-input pole placement)
#print axioms ControlsLean.Controls.top_le_span_canonVec
#print axioms ControlsLean.Controls.toMatrix_canonBasis
#print axioms ControlsLean.Controls.repr_canonBasis_b
#print axioms ControlsLean.Controls.charpoly_add_vecMulVec_eq
#print axioms ControlsLean.Controls.pole_placement

-- Addition 8 (Issue #7): Controls (Converse Discrete-Time Lyapunov Theorem)
#print axioms ControlsLean.Controls.transpose_pow
#print axioms ControlsLean.Controls.lyapunovSum_succ
#print axioms ControlsLean.Controls.lyapunovSum_succ'
#print axioms ControlsLean.Controls.stein_telescoping
#print axioms ControlsLean.Controls.lyapunovSum_dissipation
#print axioms ControlsLean.Controls.quad_stein_telescoping
#print axioms ControlsLean.Controls.lyapunovSum_transpose
#print axioms ControlsLean.Controls.quad_lyapunovSum_ge
#print axioms ControlsLean.Controls.posDef_lyapunovSum
#print axioms ControlsLean.Controls.converse_lyapunov_nilpotent
#print axioms ControlsLean.Controls.stein_eq_of_tendsto
#print axioms ControlsLean.Controls.converse_lyapunov_of_tendsto_semidef
#print axioms ControlsLean.Controls.converse_lyapunov_of_tendsto
#print axioms ControlsLean.Controls.tendsto_pow_mulVec_zero_of_converse_lyapunov

-- Addition 9: Vision (Four-Point Homography Uniqueness & Projective Frame Rigidity)
#print axioms ControlsLean.Vision.eq_diagonal_of_fixes_basis
#print axioms ControlsLean.Vision.scalars_eq_of_fixes_canonical_frame
#print axioms ControlsLean.Vision.eq_smul_one_of_fixes_canonical_frame
#print axioms ControlsLean.Vision.homography_unique_on_canonical_frame
#print axioms ControlsLean.Vision.homography_unique_four_points
#print axioms ControlsLean.Vision.two_homographies_eq_smul_of_four_points
#print axioms ControlsLean.Vision.det_frameBasisMatrix
#print axioms ControlsLean.Vision.homography_rigidity_of_general_position

-- Addition 10: Controls (MPC Recursive Feasibility & Value Function Descent)
#print axioms ControlsLean.Controls.mpc_recursive_feasibility_step
#print axioms ControlsLean.Controls.mpc_closed_loop_feasible
#print axioms ControlsLean.Controls.mpcCost_shiftInput_eq
#print axioms ControlsLean.Controls.mpc_value_descent
#print axioms ControlsLean.Controls.mpc_optimal_value_descent
#print axioms ControlsLean.Controls.mpc_closed_loop_cost_bound
#print axioms ControlsLean.Controls.lti_mpc_recursive_feasibility_step

-- Addition 11: Estimation (Multivariate Kalman Filter Joseph-Form & MMSE Trace Optimality)
#print axioms ControlsLean.Estimation.josephCov_transpose
#print axioms ControlsLean.Estimation.josephCov_opt_eq_sub
#print axioms ControlsLean.Estimation.josephCov_opt_eq_one_sub_mul
#print axioms ControlsLean.Estimation.josephCov_completion_of_squares
#print axioms ControlsLean.Estimation.quad_josephCov_nonneg
#print axioms ControlsLean.Estimation.quad_josephCov_le
#print axioms ControlsLean.Estimation.trace_josephCov_eq
#print axioms ControlsLean.Estimation.trace_josephCov_le
#print axioms ControlsLean.Estimation.trace_josephCov_le_of_psd

-- Addition 12: Bounty (Uncontested Erdős Problem Solutions, Variants & Counterexamples)
#print axioms ControlsLean.Bounty.sum_range_shifted_div_two_pow
#print axioms ControlsLean.Bounty.sum_Ioc_div_two_pow
#print axioms ControlsLean.Bounty.erdos_261_borwein_loring
#print axioms ControlsLean.Bounty.erdos_261_borwein_loring_property
#print axioms ControlsLean.Bounty.erdos_261_parts_i
#print axioms ControlsLean.Bounty.erdos_261_rafik_split
#print axioms ControlsLean.Bounty.erdos_931_counterexample_symmetric_2_7
#print axioms ControlsLean.Bounty.erdos_931_counterexample_no_strict_between_prime
#print axioms ControlsLean.Bounty.erdos_931_additional_condition_nonempty
#print axioms ControlsLean.Bounty.erdos_931_exists_prime_of_two_mul_le
#print axioms ControlsLean.Bounty.erdos_951_step_gap
#print axioms ControlsLean.Bounty.erdos_951_linear_lower_bound
#print axioms ControlsLean.Bounty.erdos_951_isBeurlingPrimes
#print axioms ControlsLean.Bounty.erdos_143_one_separated
#print axioms ControlsLean.Bounty.erdos_143_floor_injOn
#print axioms ControlsLean.Bounty.erdos_143_ncard_le_floor
#print axioms ControlsLean.Bounty.erdos_834_parts_ii
#print axioms ControlsLean.Bounty.erdos_291_three_dvd_gcd_two_mul_three_pow
#print axioms ControlsLean.Bounty.erdos_291_parts_ii
#print axioms ControlsLean.Bounty.erdos_382_lt_two_mul_of_largestPrimeRepeated
#print axioms ControlsLean.Bounty.findGreatest_mono_pred

-- Addition 13: Robotics (3D Rotation Lie Algebra so(3) & Rodrigues' Rotation Formula)
#print axioms ControlsLean.Robotics.skew_mulVec_self
#print axioms ControlsLean.Robotics.skew_sq
#print axioms ControlsLean.Robotics.skew_cube
#print axioms ControlsLean.Robotics.trace_skew
#print axioms ControlsLean.Robotics.trace_skew_sq
#print axioms ControlsLean.Robotics.skew_lie_bracket
#print axioms ControlsLean.Robotics.rodrigues_transpose
#print axioms ControlsLean.Robotics.rodrigues_mulVec_self
#print axioms ControlsLean.Robotics.rodrigues_mul_rodrigues
#print axioms ControlsLean.Robotics.rodrigues_transpose_mul_self
#print axioms ControlsLean.Robotics.rodrigues_mul_transpose_self
#print axioms ControlsLean.Robotics.trace_rodrigues

-- Addition 14: Robotics (SE(3) Spatial Adjoint & Euler–Lagrange Manipulator Passivity)
#print axioms ControlsLean.Robotics.adjoint6_one
#print axioms ControlsLean.Robotics.adjoint6_mul
#print axioms ControlsLean.Robotics.adjoint6_inv_mul
#print axioms ControlsLean.Robotics.det_adjoint6
#print axioms ControlsLean.Robotics.wrench_twist_power_invariance
#print axioms ControlsLean.Robotics.manipulator_passivity_power
#print axioms ControlsLean.Robotics.manipulator_pd_gravity_lyapunov

-- Addition 15: Controls (Discrete-Time LQR, Bellman Completion of Squares & DARE Stability)
#print axioms ControlsLean.Controls.lqrHessian_transpose
#print axioms ControlsLean.Controls.lqr_joseph_completion_of_squares
#print axioms ControlsLean.Controls.lqr_bellman_completion_of_squares
#print axioms ControlsLean.Controls.lqr_bellman_min_le
#print axioms ControlsLean.Controls.dare_lyapunov_dissipation
#print axioms ControlsLean.Controls.dare_closedLoop_tendsto_zero

-- Addition 16: Controls (Discrete-Time Control Barrier Functions & Willems Passivity)
#print axioms ControlsLean.Controls.dtcbf_step_lower_bound
#print axioms ControlsLean.Controls.dtcbf_iterate_lower_bound
#print axioms ControlsLean.Controls.dtcbf_forward_invariant
#print axioms ControlsLean.Controls.dtcbf_strict_forward_invariant
#print axioms ControlsLean.Controls.dissipative_telescoping_bound
#print axioms ControlsLean.Controls.passive_extracted_energy_bound
#print axioms ControlsLean.Controls.passive_feedback_power_balance
#print axioms ControlsLean.Controls.passive_feedback_dissipation

-- Addition 17: Controls (DARE Existence via Riccati Value Iteration)
#print axioms ControlsLean.Controls.riccatiMap_le_joseph
#print axioms ControlsLean.Controls.riccatiMap_mono
#print axioms ControlsLean.Controls.riccatiIter_le_of_certificate
#print axioms ControlsLean.Controls.riccatiMap_continuousAt
#print axioms ControlsLean.Controls.dare_exists_of_certificate
#print axioms ControlsLean.Controls.riccatiMap_standard_form
#print axioms ControlsLean.Controls.dare_standard_form
#print axioms ControlsLean.Controls.dare_stabilizing_of_certificate
#print axioms ControlsLean.Controls.certificate_of_converse_lyapunov
#print axioms ControlsLean.Controls.lqr_stabilizing_of_stabilizable

-- Addition 18: Controls (Converse Lyapunov from Schur Stability & LQR from Stabilizability)
#print axioms ControlsLean.Controls.exists_pow_contraction
#print axioms ControlsLean.Controls.summable_quad_pow_mulVec
#print axioms ControlsLean.Controls.lyapunovSum_tendsto_of_schur
#print axioms ControlsLean.Controls.lyapunov_tail_tendsto_zero_of_schur
#print axioms ControlsLean.Controls.converse_lyapunov_of_schur
#print axioms ControlsLean.Controls.lqr_exists_of_stabilizable

-- Addition 19: Controls (DARE Uniqueness: stabilizing solution is maximal & unique)
#print axioms ControlsLean.Controls.eq_zero_of_quad_eq_zero
#print axioms ControlsLean.Controls.LoewnerLE.antisymm
#print axioms ControlsLean.Controls.dare_sub_le_closedLoop
#print axioms ControlsLean.Controls.dare_le_of_stabilizing
#print axioms ControlsLean.Controls.dare_unique_of_stabilizing
#print axioms ControlsLean.Controls.dare_stabilizing_of_posDef
#print axioms ControlsLean.Controls.dare_unique_of_posDef
#print axioms ControlsLean.Controls.lqr_existsUnique_of_stabilizable

-- Addition 20: Estimation (Steady-State Kalman Filter by Duality)
#print axioms ControlsLean.Estimation.kalmanMap_standard_form
#print axioms ControlsLean.Estimation.kalmanGain_eq
#print axioms ControlsLean.Estimation.lqrClosedLoop_dual
#print axioms ControlsLean.Estimation.schur_transpose
#print axioms ControlsLean.Estimation.kalman_steady_state
#print axioms ControlsLean.Estimation.kalman_observer_error_tendsto_zero

-- Addition 21: Controls (LQR Optimality: DARE solution is the minimal infinite-horizon cost)
#print axioms ControlsLean.Controls.lqrCost_succ
#print axioms ControlsLean.Controls.riccatiIter_le_lqrCost
#print axioms ControlsLean.Controls.lqrTraj_feedback
#print axioms ControlsLean.Controls.lqrCost_feedback_eq
#print axioms ControlsLean.Controls.lqr_infinite_horizon_optimal

-- Addition 22: Controls (LQG separation-principle stability, converging-input converging-state)
#print axioms ControlsLean.Controls.norm_mulVec_le_colSum
#print axioms ControlsLean.Controls.tendsto_zero_of_block_contraction
#print axioms ControlsLean.Controls.forced_block_expansion
#print axioms ControlsLean.Controls.tendsto_zero_of_schur_forced
#print axioms ControlsLean.Controls.lqgTraj_error_step
#print axioms ControlsLean.Controls.lqgTraj_state_step
#print axioms ControlsLean.Controls.lqg_stable_of_stable_gains
#print axioms ControlsLean.Controls.lqg_closed_loop_stable

-- Addition 23: Controls (DARE Detectability, Return-Difference & Quadratic Gain-Margin Robustness)
#print axioms ControlsLean.Controls.isDetectable_iff_isStabilizable_dual
#print axioms ControlsLean.Controls.dare_dissipation_factored
#print axioms ControlsLean.Controls.dare_zero_dissipation_escape
#print axioms ControlsLean.Controls.dare_schur_of_detectable
#print axioms ControlsLean.Controls.dare_unique_of_detectable
#print axioms ControlsLean.Controls.lqr_existsUnique_of_stabilizable_detectable
#print axioms ControlsLean.Controls.lqr_infinite_horizon_optimal_of_detectable
#print axioms ControlsLean.Controls.kalman_steady_state_of_stabilizable_detectable
#print axioms ControlsLean.Controls.dare_bellman_return_difference
#print axioms ControlsLean.Controls.dare_optimal_dominates_perturbed_bellman
#print axioms ControlsLean.Controls.dare_perturbed_dissipation_ge_of_margin

-- Addition 24: Estimation (Continuous-Time CARE, HJB Trajectory Calculus & Kalman–Bucy Filter)
#print axioms ControlsLean.Estimation.care_completion_of_squares
#print axioms ControlsLean.Estimation.care_closedLoop_lyapunov_of_careResidual
#print axioms ControlsLean.Estimation.care_lie_derivative_neg
#print axioms ControlsLean.Estimation.care_hjb_nonneg_of_solution
#print axioms ControlsLean.Estimation.hasDerivAt_care_hjb
#print axioms ControlsLean.Estimation.kalmanBucyCovDeriv_completion_of_squares
#print axioms ControlsLean.Estimation.kalmanBucy_loewner_optimal
#print axioms ControlsLean.Estimation.kalmanBucy_trace_optimal
#print axioms ControlsLean.Estimation.kalmanBucy_steadyState_negDef
#print axioms ControlsLean.Estimation.hasVecDerivAt_kalmanBucy_error

-- Addition 25: Controls (Discrete-Time Input-to-State Stability & Schur Quadratic Perturbation Bounds)
#print axioms ControlsLean.Controls.iss_lyapunov_convolution_bound
#print axioms ControlsLean.Controls.iss_lyapunov_step_bound
#print axioms ControlsLean.Controls.iss_invariant_sublevel
#print axioms ControlsLean.Controls.iss_ultimate_bound
#print axioms ControlsLean.Controls.iss_tendsto_zero_of_disturbance_tendsto_zero
#print axioms ControlsLean.Controls.quad_add_peter_paul_identity
#print axioms ControlsLean.Controls.quad_add_le_peter_paul
#print axioms ControlsLean.Controls.quad_iss_of_stein_explicit
#print axioms ControlsLean.Controls.schur_quadratic_iss
#print axioms ControlsLean.Controls.schur_quadratic_iss_trajectory_bound

-- Addition 26: Bounty (New Erdős Solutions, Extremal Certificates & Structural Insights)
#print axioms ControlsLean.Bounty.erdos_370_dyadic_bounds
#print axioms ControlsLean.Bounty.erdos_370
#print axioms ControlsLean.Bounty.erdos_645_bounded_47
#print axioms ControlsLean.Bounty.erdos_645
#print axioms ControlsLean.Bounty.erdos_493
#print axioms ControlsLean.Bounty.erdos_493_strictMono_k_two
#print axioms ControlsLean.Bounty.erdos_493_two_factors_ge_three_iff
#print axioms ControlsLean.Bounty.erdos_275_dyadic_covers_Icc
#print axioms ControlsLean.Bounty.erdos_275_dyadic_misses_mul
#print axioms ControlsLean.Bounty.erdos_275_extremal_sharpness
#print axioms ControlsLean.Bounty.erdos_873_lcm_ge_add
#print axioms ControlsLean.Bounty.erdos_1125_kemperman_monotone_chain

-- Addition 27: Controls (Minimal-Hypothesis LQG Separation & Discrete-Time Bounded Real / H_inf Riccati Theory)
#print axioms ControlsLean.Controls.lqg_closed_loop_stable_of_stabilizable_detectable
#print axioms ControlsLean.Controls.hinf_stage_completion_of_squares
#print axioms ControlsLean.Controls.hinf_stage_dissipation_of_fixed
#print axioms ControlsLean.Controls.hinf_finite_horizon_identity
#print axioms ControlsLean.Controls.hinf_l2_gain_bound
#print axioms ControlsLean.Controls.hinf_worstCase_disturbance_tight
#print axioms ControlsLean.Controls.schur_of_lyapunov_le_detectable
#print axioms ControlsLean.Controls.hinf_schur_of_detectable

-- Addition 28: Controls (Nonlinear Integrator Backstepping, Recursive CLFs & Sontag's Universal Formula)
#print axioms ControlsLean.Controls.backsteppingLyapunov_posDef
#print axioms ControlsLean.Controls.backstepping_lie_deriv_eq
#print axioms ControlsLean.Controls.hasDerivAt_backstepping_lyapunov
#print axioms ControlsLean.Controls.backstepping_closedLoop_lie_deriv
#print axioms ControlsLean.Controls.hasDerivAt_backstepping_closedLoop
#print axioms ControlsLean.Controls.backstepping_dissipation_bound
#print axioms ControlsLean.Controls.backstepping_strict_negDef
#print axioms ControlsLean.Controls.backstepping_chain_telescoping
#print axioms ControlsLean.Controls.backstepping_chain_dissipation
#print axioms ControlsLean.Controls.hasDerivAt_backstepping_chain
#print axioms ControlsLean.Controls.sontag_universal_stabilizer
#print axioms ControlsLean.Controls.sontag_clf_strict_decrease
#print axioms ControlsLean.Controls.hasDerivAt_sontag_clf

-- Addition 29: Bounty (Wave 2 Erdős Solutions: #1148, #1179, #1187, #311, #367, #455)
#print axioms ControlsLean.Bounty.ErdosWave2.Erdos1148.erdos_1148.variants.weaker
#print axioms ControlsLean.Bounty.ErdosWave2.Erdos1179.sum_repCount_eq_two_pow
#print axioms ControlsLean.Bounty.ErdosWave2.Erdos1179.erdos_1179.variants.lower_bound
#print axioms ControlsLean.Bounty.ErdosWave2.Erdos1187.erdos_1187.parts.ii
#print axioms ControlsLean.Bounty.ErdosWave2.Erdos311.delta_ge_inv_lcm
#print axioms ControlsLean.Bounty.ErdosWave2.Erdos367.erdos_367.variants.k_le_two
#print axioms ControlsLean.Bounty.ErdosWave2.Erdos455.discreteConvex_quadratic_lower_bound

-- Addition 30: Estimation (POMDP Bayesian Belief Simplex & Smallwood-Sondik PWLC Value Functions)
#print axioms ControlsLean.Estimation.POMDPBelief.isBelief_convex_comb
#print axioms ControlsLean.Estimation.POMDPBelief.beliefUpdate_isBelief
#print axioms ControlsLean.Estimation.POMDPBelief.beliefPredict_isBelief
#print axioms ControlsLean.Estimation.POMDPBelief.pomdpValue_ge_dot
#print axioms ControlsLean.Estimation.POMDPBelief.exists_alpha_achieving_pomdpValue
#print axioms ControlsLean.Estimation.POMDPBelief.pomdpValue_convex
#print axioms ControlsLean.Estimation.POMDPBelief.bellman_backup_alpha_eq
#print axioms ControlsLean.Estimation.POMDPBelief.bellman_backup_normalized_eq
#print axioms ControlsLean.Estimation.POMDPBelief.bellman_backup_pwlc_preservation

-- Addition 31: Robotics (Slotine-Li Passivity Manipulator Tracking & Adaptive Control)
#print axioms ControlsLean.Robotics.slidingError_eq_velError_add
#print axioms ControlsLean.Robotics.slotine_li_closed_loop_sliding
#print axioms ControlsLean.Robotics.slotine_li_augmented_closed_loop
#print axioms ControlsLean.Robotics.skew_coriolis_power_cancel
#print axioms ControlsLean.Robotics.slotine_li_lyapunov_deriv
#print axioms ControlsLean.Robotics.slotine_li_lyapunov_deriv_neg
#print axioms ControlsLean.Robotics.slotine_li_augmented_lyapunov_deriv
#print axioms ControlsLean.Robotics.slotine_li_adaptive_lyapunov_deriv
#print axioms ControlsLean.Robotics.slotine_li_exponential_rate
#print axioms ControlsLean.Robotics.hasDerivAt_slotine_li_storage

-- Addition 32: Controls (Routh-Hurwitz criterion for cubics)
#print axioms ControlsLean.Controls.isHurwitz3_iff
#print axioms ControlsLean.Controls.isHurwitz3_of_pos
#print axioms ControlsLean.Controls.cubic_123_hurwitz
#print axioms ControlsLean.Controls.pGain_s_s1_s2_hurwitz_iff

-- Addition 33: Robotics (Unit-quaternion rotations & kinematics)
#print axioms ControlsLean.Robotics.re_rotate
#print axioms ControlsLean.Robotics.rotate_re_eq_zero
#print axioms ControlsLean.Robotics.normSq_rotate
#print axioms ControlsLean.Robotics.norm_rotate
#print axioms ControlsLean.Robotics.rotate_mul
#print axioms ControlsLean.Robotics.rotate_neg
#print axioms ControlsLean.Robotics.rotMatrix_transpose_mul_self
#print axioms ControlsLean.Robotics.rotMatrix_mul_transpose_self
#print axioms ControlsLean.Robotics.det_rotMatrix
#print axioms ControlsLean.Robotics.rotMatrix_mem_specialOrthogonalGroup
#print axioms ControlsLean.Robotics.rotMatrix_mulVec_imVec
#print axioms ControlsLean.Robotics.hasDerivAt_normSq_kinematics

-- Addition 34: Robotics (Planar two-link arm kinematics & workspace)
#print axioms ControlsLean.Robotics.det_jacobian
#print axioms ControlsLean.Robotics.det_jacobian_eq_zero_iff
#print axioms ControlsLean.Robotics.det_jacobian_eq_zero_iff_exists_int
#print axioms ControlsLean.Robotics.hasFDerivAt_fk
#print axioms ControlsLean.Robotics.jacobianCLM_apply
#print axioms ControlsLean.Robotics.hasDerivAt_fk_fst_q1
#print axioms ControlsLean.Robotics.hasDerivAt_fk_fst_q2
#print axioms ControlsLean.Robotics.hasDerivAt_fk_snd_q1
#print axioms ControlsLean.Robotics.hasDerivAt_fk_snd_q2
#print axioms ControlsLean.Robotics.radius_sq_fk
#print axioms ControlsLean.Robotics.radius_fk_le_add
#print axioms ControlsLean.Robotics.abs_sub_le_radius_fk
#print axioms ControlsLean.Robotics.fk_complex
#print axioms ControlsLean.Robotics.fk_ik
#print axioms ControlsLean.Robotics.reachable_iff

-- Addition 35: Robotics (Unicycle / differential drive & Kanayama tracking)
#print axioms ControlsLean.Robotics.diffDriveInverse_diffDrive
#print axioms ControlsLean.Robotics.diffDrive_diffDriveInverse
#print axioms ControlsLean.Robotics.diffDriveEquiv
#print axioms ControlsLean.Robotics.diffDrive_bijective
#print axioms ControlsLean.Robotics.hasDerivAt_arcX
#print axioms ControlsLean.Robotics.hasDerivAt_arcY
#print axioms ControlsLean.Robotics.hasDerivAt_arcTheta
#print axioms ControlsLean.Robotics.tendsto_arcX_straight
#print axioms ControlsLean.Robotics.tendsto_arcY_straight
#print axioms ControlsLean.Robotics.nonholonomic_constraint
#print axioms ControlsLean.Robotics.arc_nonholonomic
#print axioms ControlsLean.Robotics.hasDerivAt_errX
#print axioms ControlsLean.Robotics.hasDerivAt_errY
#print axioms ControlsLean.Robotics.hasDerivAt_errTheta
#print axioms ControlsLean.Robotics.kanayamaV_nonneg
#print axioms ControlsLean.Robotics.hasDerivAt_kanayamaV_comp
#print axioms ControlsLean.Robotics.hasDerivAt_kanayamaV
#print axioms ControlsLean.Robotics.kanayamaV_deriv_nonpos
#print axioms ControlsLean.Robotics.hasDerivAt_kanayamaV_classic
#print axioms ControlsLean.Robotics.kanayamaV_classic_deriv_nonpos

-- Addition 36: Vision (Cross-ratio projective invariance)
#print axioms ControlsLean.Vision.crossRatio_mulVec
#print axioms ControlsLean.Vision.crossRatio_smul
#print axioms ControlsLean.Vision.crossRatioAffine_mobius
#print axioms ControlsLean.Vision.crossRatioFrom_linePt
#print axioms ControlsLean.Vision.crossRatioFrom_homography
#print axioms ControlsLean.Vision.crossRatio_collinear_homography
#print axioms ControlsLean.Vision.crossRatio_midpoint_infinity
#print axioms ControlsLean.Vision.crossRatio_harmonic_homography
#print axioms ControlsLean.Vision.road_markers_mobius

-- Addition 37: Vision (Essential matrix constraints & twisted pair)
#print axioms ControlsLean.Vision.essential_mul_transpose
#print axioms ControlsLean.Vision.trace_essential_mul_transpose
#print axioms ControlsLean.Vision.essential_mul_transpose_mul_essential
#print axioms ControlsLean.Vision.essential_cubic_constraint
#print axioms ControlsLean.Vision.essential_mul_transpose_mulVec_of_orthogonal
#print axioms ControlsLean.Vision.essential_mul_transpose_mulVec_self
#print axioms ControlsLean.Vision.transpose_essential_mulVec_self
#print axioms ControlsLean.Vision.essential_twist
#print axioms ControlsLean.Vision.rotPiAbout_transpose_mul_self
#print axioms ControlsLean.Vision.det_rotPiAbout
#print axioms ControlsLean.Vision.rotPiAbout_mulVec_self
#print axioms ControlsLean.Vision.rotPiAbout_mem_specialOrthogonalGroup
#print axioms ControlsLean.Vision.rotPiAbout_mem_specialOrthogonalGroup_real

-- Addition 38: Vision (Point-cloud registration: ICP / Kabsch reductions)
#print axioms ControlsLean.Vision.registrationCost_eq
#print axioms ControlsLean.Vision.registrationCost_optimalTranslation_le
#print axioms ControlsLean.Vision.registrationCost_eq_optimal_iff
#print axioms ControlsLean.Vision.registrationCost_optimalTranslation
#print axioms ControlsLean.Vision.sum_norm_sub_sq_le_iff
#print axioms ControlsLean.Vision.registrationCost_le_of_crossCorrelation_max
#print axioms ControlsLean.Vision.sum_mulVec_dotProduct_eq_trace
#print axioms ControlsLean.Vision.sum_inner_toEuclideanLin_eq_trace
#print axioms ControlsLean.Vision.mul_cos_add_mul_sin_le
#print axioms ControlsLean.Vision.mul_cos_add_mul_sin_arg
#print axioms ControlsLean.Vision.angle_eq_arg_of_eq_sqrt
#print axioms ControlsLean.Vision.rot2Cost_arg_le

-- Addition 39: Estimation (Least squares, weighted LS & recursive LS)
#print axioms ControlsLean.Estimation.rss_eq_add_of_normal
#print axioms ControlsLean.Estimation.isLeastSquares_iff
#print axioms ControlsLean.Estimation.rss_eq_norm_sq
#print axioms ControlsLean.Estimation.det_transpose_mul_self_ne_zero
#print axioms ControlsLean.Estimation.isLeastSquares_iff_eq_inv
#print axioms ControlsLean.Estimation.isLeastSquares_iff_eq_inv_of_injective
#print axioms ControlsLean.Estimation.wrss_eq_add_of_normal
#print axioms ControlsLean.Estimation.isWeightedLeastSquares_iff
#print axioms ControlsLean.Estimation.isWeightedLeastSquares_iff_eq_inv_of_injective
#print axioms ControlsLean.Estimation.mul_shermanMorrison
#print axioms ControlsLean.Estimation.shermanMorrison_mul
#print axioms ControlsLean.Estimation.shermanMorrison_mulVec
#print axioms ControlsLean.Estimation.rlsUpdate_normal
#print axioms ControlsLean.Estimation.rlsUpdate_isLeastSquares
#print axioms ControlsLean.Estimation.lineFit_isMin_iff
#print axioms ControlsLean.Estimation.lineFit_isMin_iff_eq

-- Addition 40: Controls (Iterative learning control & Arimoto condition)
#print axioms ControlsLean.Controls.ilc_error_succ
#print axioms ControlsLean.Controls.ilc_error_eq_pow
#print axioms ControlsLean.Controls.ilc_norm_error_le
#print axioms ControlsLean.Controls.ilc_norm_error_antitone
#print axioms ControlsLean.Controls.ilc_error_tendsto_zero
#print axioms ControlsLean.Controls.ilc_input_converges
#print axioms ControlsLean.Controls.spectrum_algebraMap_add_subset
#print axioms ControlsLean.Controls.tendsto_pow_algebraMap_add_of_isNilpotent
#print axioms ControlsLean.Controls.isNilpotent_of_strictLower
#print axioms ControlsLean.Controls.one_sub_smul_lowerToeplitz_eq
#print axioms ControlsLean.Controls.arimoto_spectrum_subset
#print axioms ControlsLean.Controls.arimoto_spectralRadius_lt_one
#print axioms ControlsLean.Controls.arimoto_tendsto_pow
#print axioms ControlsLean.Controls.arimoto_error_tendsto_zero
