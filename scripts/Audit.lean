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

-- Issue #6: Estimation (Scalar Riccati iteration convergence)
#print axioms ControlsLean.Estimation.abs_riccati_iterate_sub_le
#print axioms ControlsLean.Estimation.tendsto_riccati_iterate
#print axioms ControlsLean.Estimation.tendsto_gain_riccati_iterate
