import AccelerationGuard

namespace RobotMotion.AccelerationAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Unchanged moving-goal-08 A/B event history: 20 mm then return. -/
def returnGenerous : List QEvent := [(11/50,1/50),(13/25,-1/50)]
/-- Unchanged moving-goal-08 C history, including its common execution buffer. -/
def returnBuffered : List QEvent := [(7/25,1/50),(17/25,-1/50)]

theorem old_jerk_guard_accepts : check (1/5) (15/2) 0 returnGenerous = true := by decide +kernel
theorem exact_old_acceleration_witness : qAcceleration (1/5) returnGenerous (77/100) = -21/32 := by decide +kernel
theorem new_acceleration_guard_rejects : checkAcceleration (1/5) (1/2) 0 returnGenerous = false := by decide +kernel
theorem exact_old_acceleration_peak_checked : checkAcceleration (1/5) (21/32) 0 returnGenerous = true := by decide +kernel
theorem buffered_acceleration_guard_accepts : checkAcceleration (1/5) (1/2) 0 returnBuffered = true := by decide +kernel
theorem buffered_acceleration_witness : qAcceleration (1/5) returnBuffered (22/25) = -1/2 := by decide +kernel

theorem old_real_violation :
    ¬ (∀ t : ℝ, 0 ≤ t → |acceleration (1/5) (realEvents returnGenerous) t| ≤ 1/2) := by
  intro hall
  have hv := hall (77/100) (by norm_num)
  have he := cast_qAcceleration (h:=1/5) (by norm_num) returnGenerous (77/100)
  rw [exact_old_acceleration_witness] at he
  norm_num at he
  rw [← he] at hv
  norm_num at hv

theorem buffered_real_bound : ∀ t : ℝ, 0 ≤ t →
    |acceleration (1/5) (realEvents returnBuffered) t| ≤ 1/2 := by
  have h := (checkAcceleration_real_iff (1/5) (1/2) 0 returnBuffered).mp buffered_acceleration_guard_accepts
  simpa using h.2.2

-- Degenerate and boundary cases belong to the same executable checker.
theorem empty_history : checkAcceleration 1 0 0 [] = true := by decide +kernel
theorem coincident_cancellation : checkAcceleration 1 0 0 [(0,100),(0,-100)] = true := by decide +kernel
theorem expired_history : checkAcceleration 1 0 4 [(0,1)] = true := by decide +kernel
theorem zero_width_rejected : checkAcceleration 0 1 0 [] = false := by decide +kernel
theorem negative_bound_rejected : checkAcceleration 1 (-1) 0 [] = false := by decide +kernel

/-- Knot-only checking misses the genuine off-knot maximum at 4/3. -/
theorem knot_only_false_acceptance :
    (qGuardPoints 1 0 [(0,1)]).all (fun t => decide (|qAcceleration 1 [(0,1)] t| ≤ 1/2)) = true := by decide +kernel
theorem off_knot_peak : qAcceleration 1 [(0,1)] (4/3) = 2/3 := by decide +kernel
theorem complete_guard_rejects_knot_only_case : checkAcceleration 1 (1/2) 0 [(0,1)] = false := by decide +kernel

/-- Current time is essential when the true peak is already in the past. -/
theorem current_time_violation : qAcceleration 1 [(0,1)] (7/2) = -1/8 := by decide +kernel
theorem current_time_rejects : checkAcceleration 1 (1/10) (7/2) [(0,1)] = false := by decide +kernel

def deferredReturn : List QEvent := [(11/50,1/50),(31/50,-1/50)]
theorem deferred_return_acceleration : checkAcceleration (1/5) (1/2) 0 deferredReturn = true := by decide +kernel
theorem deferred_return_jerk : check (1/5) (15/2) 0 deferredReturn = true := by decide +kernel

end RobotMotion.AccelerationAdmission
