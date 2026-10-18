module
public import QuadraticWitness
@[expose] public section
noncomputable section
namespace LeanControls.QuadraticIndependentReview
open Set
open UncertainLag (State)
open VariableResponse RobustHold ScaledTracking Settling QuadraticHold QuadraticWitness
set_option maxHeartbeats 2000000

/-- Restate the target using only the physical scalar equations and the explicit
three initial inequalities. This checks the abstractions used in the theorem. -/
theorem raw_physical_equations_suffice {H c : ℝ} (hH : 2 ≤ H)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hc : ContinuousOn f (Icc 0 H))
    (hd : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
      HasDerivAt (fun s => f s i)
        (![f t 1,f t 2,r t*(-800*(f t 0-c)-60*f t 1-(3/2)*f t 2+w t)] i) t)
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 1/100)
    (h0 : |f 0 0-c| ≤ 1/5000)
    (h1 : |f 0 0-c+f 0 1/40| ≤ 1/5000)
    (h2 : |f 0 0-c+f 0 1/20+f 0 2/1600| ≤ 1/5000) :
    ∀ t ∈ Icc 2 H, |f t 1| ≤ 1/1000 ∧ |f t 2| ≤ 1/50 := by
  have hf : IsTrajectory H r (fun t => holdInput 10 c f t+w t) f := by
    refine ⟨hc,?_⟩
    intro t ht i
    convert hd t ht i using 1 <;> fin_cases i <;>
      dsimp [holdInput,command,scaleState] <;> ring
  apply two_seconds_actual_changing_input (by linarith) hf hrlo hrhi hw
  intro i
  fin_cases i
  · simpa [coordinates,scaleState] using h0
  · convert h1 using 1 <;> dsimp [coordinates,scaleState] <;> ring
  · convert h2 using 1 <;> dsimp [coordinates,scaleState] <;> ring

theorem horizon_two_is_nonempty : (2:ℝ) ∈ Icc 2 2 := ⟨le_rfl,le_rfl⟩

theorem fixed_command_formula (c : ℝ) (f : ℝ → State) (t : ℝ) :
    holdInput 10 c f t = -800*(f t 0-c)-60*f t 1-f t 2/2 := by
  dsimp [holdInput,command,scaleState]; ring

theorem scaled_actual_velocity_and_acceleration (c : ℝ) (s : State) :
    qState c s 1 = 2000*s 1 ∧ qState c s 2 = 50*s 2 := by
  norm_num [qState]

theorem original_cube_boundary_is_not_unit_ellipsoid :
    (∀ i, |coordinates 0 (scaleState 10 (![1/5000,0,0] : State)) i| ≤ 1/5000) ∧
    1 < energy (qState 0 (![1/5000,0,0] : State) 0)
      (qState 0 (![1/5000,0,0] : State) 1) (qState 0 (![1/5000,0,0] : State) 2) := by
  constructor
  · intro i; fin_cases i <;> norm_num [coordinates,scaleState]
  · norm_num [energy,qState]

theorem changing_witness_has_large_start_and_late_guarantee :
    switchingRate 0 ≠ switchingRate 2 ∧ switchingDisturbance 0 ≠ switchingDisturbance 2 ∧
    |movingState 0 1| > 1/1000 ∧ |movingState 0 2| > 1/50 ∧
    (∀ t ∈ Icc 2 4, |movingState t 1| ≤ 1/1000 ∧ |movingState t 2| ≤ 1/50) := by
  refine ⟨inputs_really_change.1,inputs_really_change.2,
    moving_initial_exceeds_final_targets.1,moving_initial_exceeds_final_targets.2,?_⟩
  exact two_seconds_actual_changing_input (H:=4) (c:=0) (by norm_num)
    (switching_trajectory 4) (fun t ht => (switching_rate_bounds t).1)
    (fun t ht => (switching_rate_bounds t).2)
    (fun t ht => switching_disturbance_bound t) moving_initial_cube

theorem moving_witness_never_exactly_stops (t : ℝ) : movingState t 1 ≠ 0 := by
  dsimp [movingState]
  exact ne_of_lt (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _))

/-- Independent reviewer02's analytic realization is copied here and rebuilt.
It gives an actual nonzero-disturbance handoff client of this new theorem. -/
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
    · convert (hp.const_mul (2/5)).mul he using 1 <;>
        (try funext s) <;> dsimp [stepHold] <;> ring
    · convert (((hasDerivAt_id t).const_mul (4/5)).sub (hp.const_mul 16)).mul he using 1 <;>
        (try funext s) <;> dsimp [stepHold,holdInput,command,scaleState] <;> ring

theorem step_hold_matched_endpoint :
    stepHold 0 = DirectReference.reference 7 (DirectReference.duration 7) := by
  rw [DirectReference.reference_endpoint]
  ext i
  fin_cases i <;> norm_num [stepHold]

theorem full_nonzero_disturbance_composition :
    ∀ t ∈ Icc 2 4, |stepHold t 1| ≤ 1/1000 ∧ |stepHold t 2| ≤ 1/50 := by
  exact fixed_reference_then_changing_hold (H:=4) exact_reference_plant
    (by norm_num) (step_hold_trajectory 4) step_hold_matched_endpoint
    (by intro t ht; norm_num) (by intro t ht; norm_num)
    (by intro t ht; norm_num)

theorem step_hold_has_nonzero_speed_at_two : stepHold 2 1 ≠ 0 := by
  dsimp [stepHold]
  exact ne_of_gt (mul_pos (by norm_num) (Real.exp_pos _))

theorem hold_time_two_is_global_time_three_and_half :
    DirectReference.phaseStart 7 + DirectReference.duration 7 + 2 = (7/2:ℝ) := by
  rw [DirectReference.final_time]; norm_num

theorem moving_witness_does_not_match_direct_endpoint :
    movingState 0 ≠ DirectReference.reference 7 (DirectReference.duration 7) := by
  rw [DirectReference.reference_endpoint]
  intro h
  have := congrArg (fun s : State => s 0) h
  norm_num [movingState] at this

end LeanControls.QuadraticIndependentReview
