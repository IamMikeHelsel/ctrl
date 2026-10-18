import PhysicalArrival

open Set
noncomputable section
namespace IndependentMotionReview02
open RobotMotion RobotMotion.AccelerationAdmission
open LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.TrackingReplan LeanControls.ScaledTracking

def q : ℝ → State := referenceState 0 (1/5) (realEvents deferredReturn)
def j : ℝ → ℝ := jerk (1/5) (realEvents deferredReturn)
def shifted (e : ℝ) (t : ℝ) : State := ![q t 0 + e, q t 1, q t 2]

theorem shifted_continuous (e : ℝ) : Continuous (shifted e) := by
  apply continuous_pi
  intro i
  have hc := referenceState_continuous 0 (1/5) (realEvents deferredReturn)
  fin_cases i
  · exact ((continuous_apply 0).comp hc).add continuous_const
  · exact (continuous_apply 1).comp hc
  · exact (continuous_apply 2).comp hc

/-- An actual nonconstant trajectory exists for these inputs: it is exactly
the reference with a constant position offset. No ODE existence axiom is used. -/
theorem shifted_actual_trajectory (e : ℝ) :
    IsTrajectory (5/2) (fun _ => 96)
      (fun t => physicalInput 10 (shifted e) q j t + 800*e) (shifted e) := by
  constructor
  · exact (shifted_continuous e).continuousOn
  · intro t ht i
    have hd := referenceState_deriv (h:=1/5) (by norm_num) 0 (realEvents deferredReturn) t i
    fin_cases i
    · convert hd.add_const e using 1 <;> simp [shifted,q]
    · simpa [shifted,q] using hd
    · convert hd using 1 <;> simp [shifted,q,j,physicalInput] <;> ring

theorem shifted_initial_cube :
    ∀ i, |coordinates 0 (scaledError 10 (shifted (1/80000)) q 0) i| ≤ 1/5000 := by
  intro i
  fin_cases i <;> norm_num [coordinates,scaledError,scaleState,error,shifted]

theorem actual_offset_arrival :
    ∀ t ∈ Icc (71/50:ℝ) (5/2), |shifted (1/80000) t 0| ≤ 1/5000 := by
  have proof := delayed_return_physical_position
    (f:=shifted (1/80000)) (r:=fun _ => 96) (w:=fun _ => 1/100)
    (by convert shifted_actual_trajectory (1/80000) using 1 <;> norm_num [q,j])
    (by intro t ht; norm_num) (by intro t ht; norm_num)
    (by intro t ht; norm_num) (by simpa [q] using shifted_initial_cube)
  exact proof.2.2.1

theorem actual_position_need_not_equal_target : shifted (1/80000) (17/10) 0 = 1/80000 := by
  have h := (deferred_return_reference_contract.2.2.2 (17/10) (by norm_num)).1
  simpa [shifted,q,referenceState] using congrArg (fun x : ℝ => x + 1/80000) h

theorem exact_progress_lower_bound :
    (779/250000:ℝ) - 2*(1/5000) = 679/250000 ∧ (1/1000:ℝ) < 679/250000 := by
  norm_num

theorem initial_budget_margin :
    (1/100:ℝ)+(15/2)/(48*10) = 41/1600 ∧
    (41/1600:ℝ) < 2*10^2*(1/5000) := by norm_num

theorem smaller_tube_budget_fails :
    ¬ ((1/100:ℝ)+(15/2)/(48*10) ≤ 2*10^2*(1/10000)) := by norm_num

theorem retained_request_after_rejection :
    position 0 (1/5) (realEvents [(11/50,1/50)]) (17/10) = 1/50 := by
  norm_num [position,response,realEvents,realEvent,F0,P]

theorem tight_candidate_list_rejects :
    chooseExecution (1/5) (1/2) (15/2) (13/25) (13/10)
      [(11/50,1/50)] (-1/50) [13/25,31/50] = none := insufficient_candidate_deadline

theorem generous_candidate_list_accepts :
    chooseExecution (1/5) (1/2) (15/2) (13/25) (17/10)
      [(11/50,1/50)] (-1/50) [13/25,31/50] = some (31/50) := delayed_time_selected

end IndependentMotionReview02
