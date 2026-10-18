import TaskFixtures

open Set
noncomputable section
namespace IndependentTaskIntegration
open RobotMotion RobotMotion.TaskContract

theorem retained_old_complete :
    CompleteBy (1/5) (4/5) (realEvents [(0,1/100)]) := by
  norm_num [CompleteBy,realEvents,realEvent]

theorem nonempty_retained_guard :
    check (1/5) (15/2) 0 ([(0,1/100)]++[(41/50,-1/50)]) = true := by
  exact isolated_check (g0:=0) (s:=4/5) (tau:=41/50) (a:=1/100) (g:=-(1/100))
    [(0,1/100)] (by decide +kernel) retained_old_complete (by norm_num)
    (41/50) (-1/50) (by norm_num) (by norm_num) (by norm_num)

theorem nonempty_retained_midpoint :
    position 0 (1/5) (realEvents ([(0,1/100)]++[(41/50,-1/50)])) (61/50) = 0 := by
  norm_num [position,response,realEvents,realEvent,F0,P]

theorem nonempty_retained_arrival :
    position 0 (1/5) (realEvents ([(0,1/100)]++[(41/50,-1/50)])) (81/50) = -(1/100) := by
  norm_num [position,response,realEvents,realEvent,F0,P]

theorem reversed_direction_is_positive :
    directed (1/100) (-(1/100)) 0 = 1/100 := by norm_num [directed]

theorem acceleration_limit_not_jerk_guard :
    check (1/5) (15/2) 0 [(11/50,1/50),(13/25,-1/50)] = true ∧
    |acceleration (1/5) [(11/50,1/50),(13/25,-1/50)] (77/100)| = 21/32 ∧
    (1/2:ℝ) < 21/32 := by
  refine ⟨by decide +kernel,?_,by norm_num⟩
  norm_num [acceleration,response,F2,P]

end IndependentTaskIntegration
