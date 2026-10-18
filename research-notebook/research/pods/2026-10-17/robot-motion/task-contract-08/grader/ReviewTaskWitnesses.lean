import Composition

noncomputable section
namespace IndependentTaskReview
open RobotMotion
open LeanControls.UncertainLag (State)
open LeanControls.RobustHold LeanControls.ScaledTracking

/-- A future event can be fully guard-admissible while the current jet is zero. -/
theorem queued_event_passes_jerk_guard :
    check (1/5) (15/2) 0 [(1,1/50)] = true := by decide +kernel

theorem queued_event_is_currently_rest :
    position 0 (1/5) [(1,1/50)] 0 = 0 ∧
    velocity (1/5) [(1,1/50)] 0 = 0 ∧
    acceleration (1/5) [(1,1/50)] 0 = 0 ∧
    jerk (1/5) [(1,1/50)] 0 = 0 := by
  rw [jerk_eq_response (by norm_num : (0:ℝ)<1/5)]
  norm_num [position, velocity, acceleration, response, F0, F1, F2, F3, P]

theorem queued_event_breaks_reference_hold :
    position 0 (1/5) [(1,1/50)] (9/5) = 1/50 ∧
    ¬ |position 0 (1/5) [(1,1/50)] (9/5)| ≤ (1/5000:ℝ) := by
  norm_num [position, response, F0, P]

/-- This is a scalar consequence of a tracking tube, not an assumed plant theorem. -/
theorem queued_event_breaks_physical_hold {x : ℝ}
    (hx : |x-position 0 (1/5) [(1,1/50)] (9/5)| ≤ 1/5000) :
    ¬ |x| ≤ (1/5000:ℝ) := by
  rw [queued_event_breaks_reference_hold.1] at hx
  intro hh
  have hxl := (abs_le.mp hx).1
  have hxu := (abs_le.mp hh).2
  linarith

theorem fixed_midpoint_reference :
    position 0 (1/5) [(11/50,1/50)] (31/50) = (1/100:ℝ) := by
  norm_num [position, response, F0, P]

theorem fixed_midpoint_progress {x : ℝ}
    (hx : |x-position 0 (1/5) [(11/50,1/50)] (31/50)| ≤ 1/5000) :
    (49/5000:ℝ) ≤ x := by
  rw [fixed_midpoint_reference] at hx
  have hxlo := (abs_le.mp hx).1
  linarith

theorem fixed_midpoint_is_too_early_for_arrival {x : ℝ}
    (hx : |x-position 0 (1/5) [(11/50,1/50)] (31/50)| ≤ 1/5000) :
    ¬ |x-1/50| ≤ (1/5000:ℝ) := by
  rw [fixed_midpoint_reference] at hx
  intro hg
  have hxu := (abs_le.mp hx).2
  have hgl := (abs_le.mp hg).1
  linarith

theorem fixed_reference_arrival :
    position 0 (1/5) [(11/50,1/50)] (51/50) = (1/50:ℝ) := by
  norm_num [position, response, F0, P]

/-- The transformed cube alone is not the tighter benchmark endpoint test. -/
def endpointCorner : State := ![1/5000,-2/125,32/25]

theorem cube_does_not_imply_full_endpoint :
    (∀ i, |coordinates 0 (scaleState 10 endpointCorner) i| ≤ 1/5000) ∧
    ¬ |endpointCorner 1| ≤ (1/1000:ℝ) ∧
    ¬ |endpointCorner 2| ≤ (1/50:ℝ) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [coordinates, scaleState, endpointCorner]
  · norm_num [endpointCorner]
  · norm_num [endpointCorner]

end IndependentTaskReview
