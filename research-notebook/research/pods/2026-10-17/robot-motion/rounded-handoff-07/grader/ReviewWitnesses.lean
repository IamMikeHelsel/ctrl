module
public import RoundedHandoff
@[expose] public section
noncomputable section
namespace IndependentRoundedReview
open LeanControls.UncertainLag (State)
open LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.RoundedHandoff

def zeroPath : ℝ → State := fun _ => ![0,0,0]
def velocityJump : ℝ → State := fun _ => ![0,1,0]
def accelerationJump : ℝ → State := fun _ => ![0,0,1]
def unitPath : ℝ → State := fun _ => ![1,0,0]
def negativeUnitPath : ℝ → State := fun _ => ![-1,0,0]

theorem equal_position_does_not_match_velocity :
    velocityJump 0 0 = zeroPath 0 0 ∧
    |coordinates 0 (scaledError 10 zeroPath velocityJump 0) 2| = 1/20 := by
  norm_num [velocityJump, zeroPath, coordinates, scaledError, scaleState,
    LeanControls.TrackingReplan.error]

theorem equal_position_does_not_match_acceleration :
    accelerationJump 0 0 = zeroPath 0 0 ∧
    |coordinates 0 (scaledError 10 zeroPath accelerationJump 0) 2| = 1/1600 := by
  norm_num [accelerationJump, zeroPath, coordinates, scaledError, scaleState,
    LeanControls.TrackingReplan.error]

theorem omitted_reserve_fails :
    ¬ (∀ i, |coordinates 0 (scaledError 10 zeroPath velocityJump 0) i| ≤ 0) := by
  intro h
  have h2 := h 2
  rw [equal_position_does_not_match_velocity.2] at h2
  norm_num at h2

theorem radius_addition_is_sharp :
    |coordinates 0 (scaledError 10 negativeUnitPath zeroPath 0) 0| = 1 ∧
    |coordinates 0 (scaleState 10 (unitPath 0-zeroPath 0)) 0| = 1 ∧
    |coordinates 0 (scaledError 10 negativeUnitPath unitPath 0) 0| = 2 := by
  norm_num [negativeUnitPath, unitPath, zeroPath, coordinates, scaledError,
    scaleState, LeanControls.TrackingReplan.error]

theorem physical_reset_without_join_fails :
    (∀ i, |coordinates 0 (scaledError 10 zeroPath zeroPath 0) i| ≤ 0) ∧
    ¬ (∀ i, |coordinates 0 (scaledError 10 unitPath zeroPath 0) i| ≤ 0) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [zeroPath, coordinates, scaledError, scaleState,
      LeanControls.TrackingReplan.error]
  · intro h
    have h0 := h 0
    norm_num [unitPath, zeroPath, coordinates, scaledError, scaleState,
      LeanControls.TrackingReplan.error] at h0

theorem physical_input_uses_exact_feedforward
    (f q : ℝ → State) (j : ℝ → ℝ) (t : ℝ) :
    physicalInput 10 f q j t = q t 2 - 800*(f t 0-q t 0) -
      60*(f t 1-q t 1) - (f t 2-q t 2)/2+j t/96 := by
  norm_num [physicalInput]
  ring

end IndependentRoundedReview
