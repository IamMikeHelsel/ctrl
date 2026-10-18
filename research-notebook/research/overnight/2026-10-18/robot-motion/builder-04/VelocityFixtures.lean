import VelocityAdmission

namespace RobotMotion.VelocityAdmission
open AccelerationAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The declared delayed return passes all future speed bounds. -/
theorem delayed_velocity_pass :
    checkVelocity (1/5) (1/15) (13/25) [(11/50,1/50),(31/50,-1/50)] = true := by decide +kernel

theorem delayed_full_candidate_pass :
    checkVelocityTimedCandidate (1/5) (1/15) (1/2) (15/2) (13/25) (17/10)
      [(11/50,1/50)] (-1/50) (31/50) = true := by decide +kernel

theorem delayed_full_candidate_selected :
    chooseVelocityExecution (1/5) (1/15) (1/2) (15/2) (13/25) (17/10)
      [(11/50,1/50)] (-1/50) [13/25,31/50] = some (31/50) := by decide +kernel

theorem tight_deadline_no_candidate :
    chooseVelocityExecution (1/5) (1/15) (1/2) (15/2) (13/25) (13/10)
      [(11/50,1/50)] (-1/50) [13/25,31/50] = none := by decide +kernel

theorem too_small_speed_rejected :
    checkVelocity (1/5) (1/100) (13/25) [(11/50,1/50),(31/50,-1/50)] = false := by decide +kernel

theorem empty_history_pass : checkVelocity 1 0 0 [] = true := by decide +kernel
theorem zero_width_rejected : checkVelocity 0 1 0 [] = false := by decide +kernel
theorem negative_width_rejected : checkVelocity (-1) 1 0 [] = false := by decide +kernel
theorem negative_limit_rejected : checkVelocity 1 (-1) 0 [] = false := by decide +kernel
theorem expired_history_pass : checkVelocity 1 0 4 [(0,1)] = true := by decide +kernel
theorem current_inside_tail_rejected : checkVelocity 1 0 (7/2) [(0,1)] = false := by decide +kernel
theorem queued_history_rejected : checkVelocity 1 (1/2) 0 [(10,1)] = false := by decide +kernel
theorem unsorted_queued_history_pass :
    checkVelocity 1 (2/3) 0 [(10,-1),(0,1)] = true := by decide +kernel
theorem repeated_cancellation_pass :
    checkVelocity 1 0 0 [(0,100),(0,-100)] = true := by decide +kernel

/-- Every future knot passes this endpoint-only check. -/
theorem endpoint_only_passes :
    (qGuardPoints 1 0 [(0,1),(1,-1)]).all
      (fun t => decide (|qVelocity 1 [(0,1),(1,-1)] t| ≤ (1/2:ℚ))) = true := by decide +kernel

/-- A rational interior time violates that endpoint-only bound. -/
theorem interior_speed_violation :
    qVelocity 1 [(0,1),(1,-1)] (9/5) = 409/750 ∧
    (1/2:ℚ) < |qVelocity 1 [(0,1),(1,-1)] (9/5)| := by decide +kernel

theorem interior_violation_rejected :
    checkVelocity 1 (1/2) 0 [(0,1),(1,-1)] = false := by decide +kernel

/-- The original adjacent-cell check is conservative on this real history. -/
theorem conservative_rejection :
    checkVelocity 1 (1/6) 0 [(0,1),(1/4,-1)] = false := by decide +kernel

/-- Zero-valued events refine the knots but do not change the reference. -/
theorem refined_check_pass :
    checkVelocity 1 (1/6) 0 [(0,1),(1/4,-1),(1/2,0),(3/4,0)] = true := by decide +kernel

noncomputable section

/-- The rejected unrefined history actually obeys this bound at all future times.
Thus passing is sufficient; failing is not a velocity counterexample. -/
theorem rejected_history_is_safe :
    ∀ t : ℝ, 0 ≤ t → |velocity 1 [(0,1),(1/4,-1)] t| ≤ 1/6 := by
  intro t ht
  have hv := (checkVelocity_real_sound refined_check_pass).2.2 t (by simpa using ht)
  norm_num [velocity,response,realEvents,realEvent] at hv ⊢
  exact hv

/-- The rational negative witness is also a violation of the real reference. -/
theorem interior_real_violation :
    (1/2:ℝ) < |velocity 1 [(0,1),(1,-1)] (9/5)| := by
  have hv := interior_speed_violation.2
  have hc := cast_qVelocity (h:=1) (by norm_num) [(0,1),(1,-1)] (9/5)
  norm_num [realEvents,realEvent] at hc
  rw [←hc,←Rat.cast_abs]
  rw [interior_speed_violation.1]
  norm_num

/-- Nonvacuous full reference example with positive travel and a real return. -/
theorem delayed_all_three :
    (∀ t : ℝ, (13/25:ℝ) ≤ t →
      |velocity (1/5) [(11/50,1/50),(31/50,-1/50)] t| ≤ 1/15) ∧
    (∀ t : ℝ, (13/25:ℝ) ≤ t →
      |acceleration (1/5) [(11/50,1/50),(31/50,-1/50)] t| ≤ 1/2) ∧
    (∀ t : ℝ, (13/25:ℝ) ≤ t →
      |jerk (1/5) [(11/50,1/50),(31/50,-1/50)] t| ≤ 15/2) := by
  have hc := chosen_velocity_reference_contract delayed_full_candidate_selected 0
  norm_num [realEvents,realEvent] at hc ⊢
  exact ⟨hc.1,hc.2.1,hc.2.2.1⟩

end
end RobotMotion.VelocityAdmission
