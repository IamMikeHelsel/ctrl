module
public import RoundedHandoff
@[expose] public section
noncomputable section
namespace LeanControls.HandoffWitnesses
open UncertainLag (State)
open RobustHold TrackingReplan ScaledTracking RoundedHandoff

def rest : ℝ → State := fun _ => ![0,0,0]
def unitPosition : ℝ → State := fun _ => ![1,0,0]
def velocityOnly : ℝ → State := fun _ => ![0,40,0]
def accelerationOnly : ℝ → State := fun _ => ![0,0,1600]

/-- A nonzero reference join is admissible with its reserve. -/
theorem unit_jump_with_reserve :
    (∀ i, |coordinates 0 (scaledError 10 rest rest 0) i| ≤ 0) ∧
    (∀ i, |coordinates 0 (scaleState 10 (unitPosition 0-rest 0)) i| ≤ 1) ∧
    (∀ i, |coordinates 0 (scaledError 10 rest unitPosition 0) i| ≤ 1) := by
  refine ⟨?_,?_,?_⟩ <;> intro i <;> fin_cases i <;>
    norm_num [rest,unitPosition,coordinates,scaledError,scaleState,error]

theorem jump_reserve_is_necessary :
    ¬ |coordinates 0 (scaledError 10 rest unitPosition 0) 0| ≤ (0:ℝ) := by
  norm_num [rest,unitPosition,coordinates,scaledError,scaleState,error]

/-- Equal reference position does not erase a velocity join. -/
theorem velocity_join_is_visible :
    velocityOnly 0 0 = rest 0 0 ∧
    coordinates 0 (scaleState 10 (velocityOnly 0-rest 0)) 1 = 1 ∧
    coordinates 0 (scaleState 10 (velocityOnly 0-rest 0)) 2 = 2 := by
  norm_num [rest,velocityOnly,coordinates,scaleState]

/-- Equal position and velocity do not erase an acceleration join. -/
theorem acceleration_join_is_visible :
    accelerationOnly 0 0 = rest 0 0 ∧ accelerationOnly 0 1 = rest 0 1 ∧
    coordinates 0 (scaleState 10 (accelerationOnly 0-rest 0)) 2 = 1 := by
  norm_num [rest,accelerationOnly,coordinates,scaleState]

/-- An unbounded physical reset is not covered by a zero reference-jump reserve. -/
theorem physical_matching_is_necessary :
    (∀ i, |coordinates 0 (scaleState 10 (rest 0-rest 0)) i| ≤ 0) ∧
    ¬ |coordinates 0 (scaledError 10 unitPosition rest 0) 0| ≤ (0:ℝ) := by
  constructor
  · intro i; fin_cases i <;> norm_num [rest,coordinates,scaleState]
  · norm_num [rest,unitPosition,coordinates,scaledError,scaleState,error]

theorem handoff_plus_sign_is_false :
    coordinates 0 (scaledError 10 rest unitPosition 0) 0 ≠
      coordinates 0 (scaledError 10 rest rest 0) 0 +
        coordinates 0 (scaleState 10 (unitPosition 0-rest 0)) 0 := by
  norm_num [rest,unitPosition,coordinates,scaledError,scaleState,error]

theorem reserve_accumulates :
    radius 0 (fun _ => 1) 2 = 2 ∧ ¬ radius 0 (fun _ => 1) 2 ≤ (1:ℝ) := by
  norm_num [constant_radius]

/-- The proposed scalar numerical budget is exact, before jump inflation. -/
theorem fixed_budget_equality :
    (1:ℝ)/100 + (15/2)/(48*10) = 2*10^2*(41/320000) := by norm_num

theorem fixed_uniform_radius_in_millimetres :
    1000*radius (41/320000) (fun _ => 1/10^15) 188 =
      (128125000188:ℝ)/10^12 := by
  rw [constant_radius]
  norm_num

end LeanControls.HandoffWitnesses
