module
public import DirectBias
public import BiasWitness
@[expose] public section
noncomputable section
namespace LeanControls.ConstantBiasIndependentReview
open Set
open UncertainLag (State)
open VariableResponse RobustHold ScaledTracking Settling ConstantBias BiasFixtures BiasWitness DirectBias

theorem exact_reference_plant :
    DirectReference.DirectPlant DirectReference.reference (fun _ _ => 96) (fun _ _ => 0) := by
  constructor
  · intro k hk
    constructor
    · exact (DirectReference.reference_continuous k).continuousOn
    · intro t ht i
      convert DirectReference.reference_derivatives k t i using 1 <;>
        fin_cases i <;> dsimp [physicalInput] <;> ring
  · intro k hk t ht; norm_num
  · intro k hk t ht; norm_num
  · intro k hk t ht; norm_num
  · exact DirectReference.reference_matches
  · exact DirectReference.reference_initial

/-- Start at the exact endpoint, then apply a nonzero constant physical bias.
This is an actual trajectory of the original controller, not a retargeted one. -/
def stepHold (t : ℝ) : State :=
  ![3/5+(1/80000)*(1-(1+40*t+800*t^2)*Real.exp (-40*t)),
    (2/5)*t^2*Real.exp (-40*t), ((4/5)*t-16*t^2)*Real.exp (-40*t)]

theorem step_hold_trajectory (H : ℝ) :
    IsTrajectory H (fun _ => 80)
      (fun t => holdInput 10 (3/5) stepHold t+(1/100:ℝ)) stepHold := by
  constructor
  · apply continuousOn_pi.mpr
    intro i
    fin_cases i <;> dsimp [stepHold] <;> fun_prop
  · intro t ht i
    have he := (((hasDerivAt_id t).const_mul (-40:ℝ)).exp)
    have hp := (hasDerivAt_id t).pow 2
    have hq := ((hasDerivAt_const t (1:ℝ)).add ((hasDerivAt_id t).const_mul 40)).add
      (hp.const_mul 800)
    fin_cases i
    · convert (((hasDerivAt_const t (1:ℝ)).sub (hq.mul he)).const_mul (1/80000)).const_add (3/5) using 1 <;>
        dsimp [stepHold] <;> ring
    · convert (hp.const_mul (2/5)).mul he using 1 <;> dsimp [stepHold] <;> ring
    · convert (((hasDerivAt_id t).const_mul (4/5)).sub (hp.const_mul 16)).mul he using 1 <;>
        dsimp [stepHold,holdInput,command,scaleState] <;> ring

theorem step_hold_matched_endpoint :
    stepHold 0 = DirectReference.reference 7 (DirectReference.duration 7) := by
  rw [DirectReference.reference_endpoint]
  ext i
  fin_cases i <;> norm_num [stepHold]

/-- H=2, nonzero bias, full DirectPlant, and unchanged endpoint: the concrete
composition has a nonempty realization at its certified endpoint. -/
theorem full_nonzero_bias_composition_at_two :
    |stepHold 2 0-3/5| ≤ 1109/81920000 ∧
      |stepHold 2 1| ≤ 17/204800 ∧ |stepHold 2 2| ≤ 17/2560 := by
  exact fixed_reference_bias_endpoint (H:=2) (b:=1/100) exact_reference_plant
    (by norm_num) (by norm_num) (step_hold_trajectory 2) step_hold_matched_endpoint
    (by intro t ht; norm_num) (by intro t ht; norm_num)

theorem step_hold_nonzero_velocity_at_two : stepHold 2 1 ≠ 0 := by
  dsimp [stepHold]
  exact ne_of_gt (mul_pos (by norm_num) (Real.exp_pos _))

theorem true_global_time :
    DirectReference.phaseStart 7 + DirectReference.duration 7 + 2 = (7/2:ℝ) := by
  rw [DirectReference.final_time]
  norm_num

/-- The adverse sign of the original initial cube needs the larger analysis box. -/
theorem shifted_cube_enlargement_is_exact :
    |coordinates (offset 10 (1/100)) (scaleState 10 (![-(1/5000),0,0] : State)) 0| =
      (17/80000:ℝ) := by
  norm_num [coordinates,scaleState,offset]

theorem omitted_cube_enlargement_is_false :
    ¬ |coordinates (offset 10 (1/100)) (scaleState 10 (![-(1/5000),0,0] : State)) 0| ≤
      (1/5000:ℝ) := by
  norm_num [coordinates,scaleState,offset]

/-- Both bias signs use the correct physical sign in the original controller. -/
theorem negative_bias_field_identity :
    holdInput 10 0 (fun _ => (![0,0,0] : State)) 0-(1/100:ℝ) =
      holdInput 10 (-(1/80000)) (fun _ => (![0,0,0] : State)) 0 := by
  norm_num [holdInput,command,scaleState]

theorem changed_goal_is_not_same_controller :
    holdInput 10 (offset 10 (1/100)) biasedRest 0 - holdInput 10 0 biasedRest 0 = (1/100:ℝ) := by
  norm_num [holdInput,command,scaleState,offset,biasedRest]

theorem original_command_is_nonzero_at_biased_rest :
    holdInput 10 0 biasedRest 2 = -(1/100:ℝ) ∧
      holdInput 10 0 biasedRest 2+(1/100:ℝ) = 0 := by
  norm_num [holdInput,command,scaleState,biasedRest]

theorem omitting_command_bias_is_false :
    ¬ |holdInput 10 0 biasedRest 2| ≤ 24*(10:ℝ)^2*(17/16384000) := by
  norm_num [holdInput,command,scaleState,biasedRest]

theorem retained_initial_velocity_and_final_tolerance :
    biasedMotion 0 1 = -(1/250:ℝ) ∧
      |biasedMotion 2 0| ≤ 1109/81920000 ∧
      |biasedMotion 2 1| ≤ 17/204800 ∧ |biasedMotion 2 2| ≤ 17/2560 :=
  ⟨biased_motion_nonzero_initial_velocity,biased_motion_certified_at_two_seconds⟩

theorem retained_motion_not_exact_rest_at_two : biasedMotion 2 1 ≠ 0 := by
  dsimp [biasedMotion]
  exact ne_of_lt (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _))

end LeanControls.ConstantBiasIndependentReview
