import SuccessorGuard

namespace IndependentSuccessorReview

open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.AccelerationAdmission.SuccessorCheck

set_option maxRecDepth 100000

set_option maxHeartbeats 0

theorem boundary_0 : checkSuccessor (1/1 : ℚ) (0/1 : ℚ) (0/1 : ℚ) [] = true := by decide +kernel

theorem below_0 : checkSuccessor (1/1 : ℚ) (-1/1000 : ℚ) (0/1 : ℚ) [] = false := by decide +kernel

theorem boundary_1 : checkSuccessor (1/1 : ℚ) (2/3 : ℚ) (0/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ))] = true := by decide +kernel

theorem below_1 : checkSuccessor (1/1 : ℚ) (1997/3000 : ℚ) (0/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ))] = false := by decide +kernel

theorem boundary_2 : checkSuccessor (1/1 : ℚ) (1/8 : ℚ) (7/2 : ℚ) [((0/1 : ℚ),(1/1 : ℚ))] = true := by decide +kernel

theorem below_2 : checkSuccessor (1/1 : ℚ) (31/250 : ℚ) (7/2 : ℚ) [((0/1 : ℚ),(1/1 : ℚ))] = false := by decide +kernel

theorem boundary_3 : checkSuccessor (1/1 : ℚ) (0/1 : ℚ) (4/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ))] = true := by decide +kernel

theorem below_3 : checkSuccessor (1/1 : ℚ) (-1/1000 : ℚ) (4/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ))] = false := by decide +kernel

theorem boundary_4 : checkSuccessor (1/1 : ℚ) (15/7 : ℚ) (2/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ)),((1/1 : ℚ),(2/1 : ℚ)),((2/1 : ℚ),(3/1 : ℚ))] = true := by decide +kernel

theorem below_4 : checkSuccessor (1/1 : ℚ) (14993/7000 : ℚ) (2/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ)),((1/1 : ℚ),(2/1 : ℚ)),((2/1 : ℚ),(3/1 : ℚ))] = false := by decide +kernel

theorem boundary_5 : checkSuccessor (1/1 : ℚ) (33/16 : ℚ) (1/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ)),((1/1 : ℚ),(3/1 : ℚ))] = true := by decide +kernel

theorem below_5 : checkSuccessor (1/1 : ℚ) (4123/2000 : ℚ) (1/1 : ℚ) [((0/1 : ℚ),(1/1 : ℚ)),((1/1 : ℚ),(3/1 : ℚ))] = false := by decide +kernel

theorem boundary_6 : checkSuccessor (1/2 : ℚ) (16/3 : ℚ) (-1/3 : ℚ) [((-2/1 : ℚ),(1/1 : ℚ)),((0/1 : ℚ),(-2/1 : ℚ)),((2/1 : ℚ),(1/1 : ℚ))] = true := by decide +kernel

theorem below_6 : checkSuccessor (1/2 : ℚ) (15997/3000 : ℚ) (-1/3 : ℚ) [((-2/1 : ℚ),(1/1 : ℚ)),((0/1 : ℚ),(-2/1 : ℚ)),((2/1 : ℚ),(1/1 : ℚ))] = false := by decide +kernel

theorem boundary_7 : checkSuccessor (1/1 : ℚ) (0/1 : ℚ) (3/2 : ℚ) [((0/1 : ℚ),(100/1 : ℚ)),((0/1 : ℚ),(-100/1 : ℚ))] = true := by decide +kernel

theorem below_7 : checkSuccessor (1/1 : ℚ) (-1/1000 : ℚ) (3/2 : ℚ) [((0/1 : ℚ),(100/1 : ℚ)),((0/1 : ℚ),(-100/1 : ℚ))] = false := by decide +kernel

theorem boundary_8 : checkSuccessor (1/5 : ℚ) (1/2 : ℚ) (13/25 : ℚ) [((11/50 : ℚ),(1/50 : ℚ)),((31/50 : ℚ),(-1/50 : ℚ))] = true := by decide +kernel

theorem below_8 : checkSuccessor (1/5 : ℚ) (499/1000 : ℚ) (13/25 : ℚ) [((11/50 : ℚ),(1/50 : ℚ)),((31/50 : ℚ),(-1/50 : ℚ))] = false := by decide +kernel

theorem boundary_9 : checkSuccessor (2/1 : ℚ) (1/3 : ℚ) (-4/1 : ℚ) [((3/1 : ℚ),(-1/1 : ℚ)),((-2/1 : ℚ),(2/1 : ℚ)),((3/1 : ℚ),(1/1 : ℚ))] = true := by decide +kernel

theorem below_9 : checkSuccessor (2/1 : ℚ) (997/3000 : ℚ) (-4/1 : ℚ) [((3/1 : ℚ),(-1/1 : ℚ)),((-2/1 : ℚ),(2/1 : ℚ)),((3/1 : ℚ),(1/1 : ℚ))] = false := by decide +kernel

theorem boundary_10 : checkSuccessor (1/1 : ℚ) (2/3 : ℚ) (0/1 : ℚ) [((10/1 : ℚ),(1/1 : ℚ))] = true := by decide +kernel

theorem below_10 : checkSuccessor (1/1 : ℚ) (1997/3000 : ℚ) (0/1 : ℚ) [((10/1 : ℚ),(1/1 : ℚ))] = false := by decide +kernel

theorem boundary_11 : checkSuccessor (1/5 : ℚ) (21/32 : ℚ) (13/25 : ℚ) [((11/50 : ℚ),(1/50 : ℚ)),((13/25 : ℚ),(-1/50 : ℚ))] = true := by decide +kernel

theorem below_11 : checkSuccessor (1/5 : ℚ) (2621/4000 : ℚ) (13/25 : ℚ) [((11/50 : ℚ),(1/50 : ℚ)),((13/25 : ℚ),(-1/50 : ℚ))] = false := by decide +kernel

theorem exact_successor : qNext [3,0,1,1,2] 1 = some 2 := by decide +kernel

theorem fractional_current_successor : qNext [3,0,1,1,2] (3/2) = some 2 := by decide +kernel

theorem repeated_end : qNext [3,3,3] 3 = none := by decide +kernel

theorem endpoint_peak_passes_but_interior_fails : |qAcceleration 1 [(0,1)] 1| ≤ (1/2:ℚ) ∧ |qAcceleration 1 [(0,1)] 2| ≤ (1/2:ℚ) ∧ (1/2:ℚ) < |qAcceleration 1 [(0,1)] (4/3)| := by decide +kernel

theorem acceleration_acceptance_does_not_imply_small_jerk : checkSuccessor 1 (2/3) 0 [(0,1)] = true ∧ (1/10:ℚ) < qJerk 1 [(0,1)] 1 := by decide +kernel

end IndependentSuccessorReview
