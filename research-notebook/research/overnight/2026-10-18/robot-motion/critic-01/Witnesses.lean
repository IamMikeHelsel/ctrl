import TimedAdmission

namespace IndependentMotionReview

open RobotMotion RobotMotion.AccelerationAdmission

set_option maxRecDepth 100000

set_option maxHeartbeats 0

theorem oracle_boundary_0 : checkAcceleration (1/1 : ℚ) (0/1 : ℚ) (0/1 : ℚ) [] = true := by decide +kernel

theorem oracle_boundary_1 : checkAcceleration (1/1 : ℚ) (2/3 : ℚ) (0/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ))] = true := by decide +kernel

theorem oracle_strict_rejection_1 : checkAcceleration (1/1 : ℚ) (1997/3000 : ℚ) (0/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ))] = false := by decide +kernel

theorem oracle_boundary_2 : checkAcceleration (1/1 : ℚ) (1/8 : ℚ) (7/2 : ℚ) [((0/1 : ℚ),(1/1 : ℚ))] = true := by decide +kernel

theorem oracle_strict_rejection_2 : checkAcceleration (1/1 : ℚ) (31/250 : ℚ) (7/2 : ℚ) [((0/1 : ℚ),(1/1 : ℚ))] = false := by decide +kernel

theorem oracle_boundary_3 : checkAcceleration (1/1 : ℚ) (0/1 : ℚ) (4/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ))] = true := by decide +kernel

theorem oracle_boundary_4 : checkAcceleration (1/1 : ℚ) (15/7 : ℚ) (2/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ)),((1/1 : ℚ),(2/1 : ℚ)),((2/1 : ℚ),(3/1 : ℚ))] = true := by decide +kernel

theorem oracle_strict_rejection_4 : checkAcceleration (1/1 : ℚ) (14993/7000 : ℚ) (2/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ)),((1/1 : ℚ),(2/1 : ℚ)),((2/1 : ℚ),(3/1 : ℚ))] = false := by decide +kernel

theorem oracle_boundary_5 : checkAcceleration (1/1 : ℚ) (33/16 : ℚ) (1/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ)),((1/1 : ℚ),(3/1 : ℚ))] = true := by decide +kernel

theorem oracle_strict_rejection_5 : checkAcceleration (1/1 : ℚ) (4123/2000 : ℚ) (1/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ)),((1/1 : ℚ),(3/1 : ℚ))] = false := by decide +kernel

theorem oracle_boundary_6 : checkAcceleration (1/2 : ℚ) (16/3 : ℚ) (-1/3 : ℚ) [((-2/1 : ℚ),(1/1 : ℚ)),((0/1 : ℚ),(-2/1 : ℚ)),((2/1 : ℚ),(1/1 : ℚ))] = true := by decide +kernel

theorem oracle_strict_rejection_6 : checkAcceleration (1/2 : ℚ) (15997/3000 : ℚ) (-1/3 : ℚ) [((-2/1 : ℚ),(1/1 : ℚ)),((0/1 : ℚ),(-2/1 : ℚ)),((2/1 : ℚ),(1/1 : ℚ))] = false := by decide +kernel

theorem oracle_boundary_7 : checkAcceleration (1/1 : ℚ) (0/1 : ℚ) (3/2 : ℚ) [((0/1 : ℚ),(100/1 : ℚ)),((0/1 : ℚ),(-100/1 : ℚ))] = true := by decide +kernel

theorem oracle_boundary_8 : checkAcceleration (1/5 : ℚ) (1/2 : ℚ) (13/25 : ℚ) [((11/50 : ℚ),(1/50 : ℚ)),((31/50 : ℚ),(-1/50 : ℚ))] = true := by decide +kernel

theorem oracle_strict_rejection_8 : checkAcceleration (1/5 : ℚ) (499/1000 : ℚ) (13/25 : ℚ) [((11/50 : ℚ),(1/50 : ℚ)),((31/50 : ℚ),(-1/50 : ℚ))] = false := by decide +kernel

theorem oracle_boundary_9 : checkAcceleration (2/1 : ℚ) (1/3 : ℚ) (-4/1 : ℚ) [((3/1 : ℚ),(-1/1 : ℚ)),((-2/1 : ℚ),(2/1 : ℚ)),((3/1 : ℚ),(1/1 : ℚ))] = true := by decide +kernel

theorem oracle_strict_rejection_9 : checkAcceleration (2/1 : ℚ) (997/3000 : ℚ) (-4/1 : ℚ) [((3/1 : ℚ),(-1/1 : ℚ)),((-2/1 : ℚ),(2/1 : ℚ)),((3/1 : ℚ),(1/1 : ℚ))] = false := by decide +kernel

theorem plateau_nonzero : qAcceleration 1 [(0,1),(1,2),(2,3)] (5/2) = 1 := by decide +kernel

theorem plateau_zero_jerk : qJerk 1 [(0,1),(1,2),(2,3)] (5/2) = 0 := by decide +kernel

theorem constant_nonzero_jerk : qJerk 1 [(0,1),(1,3)] 1 = 1 ∧ qJerk 1 [(0,1),(1,3)] 2 = 1 := by decide +kernel

theorem future_commitment_rejected : checkTimedCandidate 1 100 100 0 4 [(10,0)] 1 0 = false := by decide +kernel

theorem empty_candidate_list_rejected : chooseExecution (1/5) (1/2) (15/2) (13/25) (17/10) [(11/50,1/50)] (-1/50) [] = none := by rfl

theorem omitted_feasible_candidate : checkTimedCandidate (1/5) (1/2) (15/2) (13/25) (17/10) [(11/50,1/50)] (-1/50) (31/50) = true := by decide +kernel

theorem zero_goal_delta_is_not_inferred : checkTimedCandidate 1 100 100 0 4 [] 1 0 = true := by decide +kernel

theorem accepted_target_is_sum : position 0 1 (realEvents [(0,1)]) 4 = 1 := by
  norm_num [position,response,realEvents,realEvent,F0,P]

theorem admitted_reference_can_exceed_arbitrary_velocity_limit : velocity 1 (realEvents [(0,1)]) 2 = 2/3 := by
  norm_num [velocity,response,realEvents,realEvent,F1,P]

end IndependentMotionReview
