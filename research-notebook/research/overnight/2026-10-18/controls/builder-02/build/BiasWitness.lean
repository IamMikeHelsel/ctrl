module
public import BiasFixtures
@[expose] public section
noncomputable section
namespace LeanControls.BiasWitness
open Set
open UncertainLag (State)
open VariableResponse RobustHold ScaledTracking Settling ConstantBias BiasFixtures

def biasedRest : ℝ → State := fun _ => ![1/80000,0,0]

theorem biased_rest_trajectory (H : ℝ) (r : ℝ → ℝ) :
    IsTrajectory H r (fun t => holdInput 10 0 biasedRest t+(1/100:ℝ)) biasedRest := by
  convert equilibrium_trajectory (by norm_num : (0:ℝ)<10) H 0 (1/100) r using 1 <;>
    norm_num [offset,biasedRest] <;> rfl

theorem biased_rest_initial :
    ∀ i, |coordinates 0 (scaleState 10 (biasedRest 0)) i| ≤ 1/5000 := by
  intro i
  fin_cases i <;> norm_num [coordinates,scaleState,biasedRest]

theorem biased_rest_certified_at_two_seconds :
    |biasedRest 2 0| ≤ 1109/81920000 ∧
      |biasedRest 2 1| ≤ 17/204800 ∧ |biasedRest 2 2| ≤ 17/2560 := by
  simpa using two_second_endpoint (H:=2) (c:=0) (b:=1/100)
    (by norm_num) (by norm_num) (biased_rest_trajectory 2 (fun _ => 80))
    (by intro t ht; norm_num) (by intro t ht; norm_num) biased_rest_initial

/-- The offset sign is fixed by the actual vector field. -/
theorem wrong_sign_is_false :
    holdInput 10 0 (fun _ => (![0,0,0] : State)) 0+(1/100:ℝ) ≠
      holdInput 10 (0-offset 10 (1/100)) (fun _ => (![0,0,0] : State)) 0 := by
  norm_num [holdInput,command,scaleState,offset]

/-- Changing the command goal would add the bias twice. At the actual
equilibrium, the changed command produces a nonzero acceleration derivative. -/
theorem changed_command_double_counts :
    80*(holdInput 10 0 biasedRest 0+(1/100:ℝ)-biasedRest 0 2) = 0 ∧
    80*(holdInput 10 (offset 10 (1/100)) biasedRest 0+(1/100:ℝ)-biasedRest 0 2) = 4/5 := by
  norm_num [holdInput,command,scaleState,offset,biasedRest]

/-- Even at exact rest, dropping the true-goal offset makes this proposed
two-second position bound false. -/
theorem no_position_offset_is_false :
    ¬ |biasedRest 2 0-(0:ℝ)| ≤ 17/16384000 := by
  norm_num [biasedRest]

/-- A nonzero initial velocity is retained with a constant nonzero bias. -/
def biasedMotion (t : ℝ) : State :=
  ![1/80000+(1/10000)*Real.exp (-40*t),
    -(1/250)*Real.exp (-40*t), (4/25)*Real.exp (-40*t)]

theorem biased_motion_trajectory (H : ℝ) :
    IsTrajectory H (fun _ => 80)
      (fun t => holdInput 10 0 biasedMotion t+(1/100:ℝ)) biasedMotion := by
  constructor
  · apply continuousOn_pi.mpr
    intro i
    fin_cases i <;> dsimp [biasedMotion] <;> fun_prop
  · intro t ht i
    have he := (((hasDerivAt_id t).const_mul (-40:ℝ)).exp)
    fin_cases i
    · convert (he.const_mul (1/10000)).const_add (1/80000) using 1 <;>
        dsimp [biasedMotion] <;> ring
    · convert he.const_mul (-(1/250)) using 1 <;> dsimp [biasedMotion] <;> ring
    · convert he.const_mul (4/25) using 1 <;>
        dsimp [biasedMotion,holdInput,command,scaleState] <;> ring

theorem biased_motion_initial :
    ∀ i, |coordinates 0 (scaleState 10 (biasedMotion 0)) i| ≤ 1/5000 := by
  intro i
  fin_cases i <;> norm_num [coordinates,scaleState,biasedMotion]

theorem biased_motion_nonzero_initial_velocity : biasedMotion 0 1 = -(1/250:ℝ) := by
  norm_num [biasedMotion]

theorem biased_motion_certified_at_two_seconds :
    |biasedMotion 2 0| ≤ 1109/81920000 ∧
      |biasedMotion 2 1| ≤ 17/204800 ∧ |biasedMotion 2 2| ≤ 17/2560 := by
  simpa using two_second_endpoint (H:=2) (c:=0) (b:=1/100)
    (by norm_num) (by norm_num) (biased_motion_trajectory 2)
    (by intro t ht; norm_num) (by intro t ht; norm_num) biased_motion_initial

end LeanControls.BiasWitness
