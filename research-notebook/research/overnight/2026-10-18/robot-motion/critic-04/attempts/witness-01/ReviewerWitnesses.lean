import VelocityFixtures
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.VelocityAdmission
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem arbitrary_signed_finite_history (h V c : ℚ) (events : List QEvent)
    (accepted : checkVelocity h V c events = true) :
    ∀ t : ℝ, (c:ℝ) ≤ t → |velocity (h:ℝ) (realEvents events) t| ≤ (V:ℝ) :=
  (checkVelocity_real_sound accepted).2.2

theorem real_delayed_speed : ∀ t : ℝ, 13/25 ≤ t →
    |velocity (1/5) [(11/50,1/50),(31/50,-1/50)] t| ≤ 1/15 := by
  have h := (chosen_velocity_reference_contract delayed_full_candidate_selected 0).2.1
  norm_num [realEvents,realEvent] at h
  exact h

theorem real_delayed_reference_rest : ∀ t : ℝ, 17/10 ≤ t →
    position 0 (1/5) [(11/50,1/50),(31/50,-1/50)] t = 0 ∧
    velocity (1/5) [(11/50,1/50),(31/50,-1/50)] t = 0 ∧
    acceleration (1/5) [(11/50,1/50),(31/50,-1/50)] t = 0 ∧
    jerk (1/5) [(11/50,1/50),(31/50,-1/50)] t = 0 := by
  have h := (chosen_velocity_reference_contract delayed_full_candidate_selected 0).2.2.2.2.2
  norm_num [realEvents,realEvent] at h
  exact h

theorem real_delayed_prefix : ∀ t : ℝ, t ≤ 31/50 →
    referenceJet 0 (1/5) [(11/50,1/50),(31/50,-1/50)] t =
      referenceJet 0 (1/5) [(11/50,1/50)] t := by
  have h := (chosen_velocity_reference_contract delayed_full_candidate_selected 0).2.2.2.2.1
  norm_num [realEvents,realEvent] at h
  exact h

theorem zero_event_preserves_velocity (h t tau : ℝ) (events : List Event) :
    velocity h (events++[(tau,0)]) t = velocity h events t := by
  simp [velocity,response,List.sum_append]

theorem cancelled_events_preserve_velocity (h t tau delta : ℝ) (events : List Event) :
    velocity h (events++[(tau,delta),(tau,-delta)]) t = velocity h events t := by
  simp [velocity,response,List.sum_append]

theorem strict_successor_duplicates :
    SuccessorCheck.qNext [1,1,0,2,2,3] 1 = some 2 := by decide +kernel
theorem strict_successor_maximum :
    SuccessorCheck.qNext [2,2,1] 2 = none := by decide +kernel
theorem invalid_width_nonempty : checkVelocity 0 100 0 [(0,1)] = false := by decide +kernel
theorem negative_bound_empty : checkVelocity 1 (-1) 0 [] = false := by decide +kernel
theorem exact_current_rejection : checkVelocity 1 (1/2) 2 [(0,1)] = false := by decide +kernel
theorem current_after_tail : checkVelocity 1 0 (9/2) [(0,1)] = true := by decide +kernel

theorem safe_rejection_exists : ∃ es : List QEvent,
    checkVelocity 1 (1/6) 0 es = false ∧
    (∀ t : ℝ, 0 ≤ t → |velocity 1 (realEvents es) t| ≤ 1/6) := by
  refine ⟨[(0,1),(1/4,-1)],conservative_rejection,?_⟩
  simpa [realEvents,realEvent] using rejected_history_is_safe

theorem actual_endpoint_failure : ∃ t : ℝ, 0 ≤ t ∧
    1/2 < |velocity 1 [(0,1),(1,-1)] t| :=
  ⟨9/5,by norm_num,interior_real_violation⟩

theorem no_return_test_accepts_tight_deadline :
    ∀ tau ∈ ([13/25,31/50] : List ℚ),
      checkVelocityTimedCandidate (1/5) (1/15) (1/2) (15/2) (13/25) (13/10)
        [(11/50,1/50)] (-1/50) tau = false :=
  (choose_velocity_none_iff _ _ _ _ _ _ _ _ _).mp tight_deadline_no_candidate
