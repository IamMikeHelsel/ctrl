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

-- Addition 13: Controls (Discrete Algebraic Riccati Equation & LQR Completion of Squares)
#print axioms ControlsLean.Controls.inputGram_transpose
#print axioms ControlsLean.Controls.quad_inputGram_nonneg
#print axioms ControlsLean.Controls.bellmanResidual_opt_eq
#print axioms ControlsLean.Controls.bellman_completion_of_squares
#print axioms ControlsLean.Controls.bellmanResidual_eq_zero_of_dare
#print axioms ControlsLean.Controls.bellmanResidual_eq_of_dare
#print axioms ControlsLean.Controls.quad_bellman_le
#print axioms ControlsLean.Controls.quad_bellman_nonneg_of_dare
#print axioms ControlsLean.Controls.dare_closed_loop_lyapunov
#print axioms ControlsLean.Controls.dare_closed_loop_dissipation
#print axioms ControlsLean.Controls.dare_closed_loop_tendsto_zero
#print axioms ControlsLean.Controls.dare_closed_loop_tendsto_zero_of_posDef_Q

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
