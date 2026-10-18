module
public import QuadraticTrajectory
public import DirectReference
@[expose] public section
noncomputable section
namespace LeanControls.QuadraticWitness
open Set
open UncertainLag (State)
open VariableResponse RobustHold ScaledTracking Settling SettlingFixtures QuadraticHold
set_option maxHeartbeats 2000000

def switchingRate (t : ℝ) : ℝ := if t ≤ 1 then 80 else 120

def switchingDisturbance (t : ℝ) : ℝ :=
  if t ≤ 1 then 0 else (4/75)*Real.exp (-40*t)

def movingState (t : ℝ) : State :=
  ![(1/5000)*Real.exp (-40*t),-(1/125)*Real.exp (-40*t),
    (8/25)*Real.exp (-40*t)]

/-- Both rate and disturbance change, while this supplied physical trajectory
remains classical. This is a witness, not a trajectory-existence theorem. -/
theorem switching_trajectory (H : ℝ) :
    IsTrajectory H switchingRate
      (fun t => holdInput 10 0 movingState t+switchingDisturbance t) movingState := by
  constructor
  · apply continuousOn_pi.mpr; intro i
    fin_cases i <;> dsimp [movingState] <;> fun_prop
  · intro t ht i
    have he := (((hasDerivAt_id t).const_mul (-40:ℝ)).exp)
    fin_cases i
    · convert he.const_mul (1/5000:ℝ) using 1 <;> dsimp [movingState] <;> ring
    · convert he.const_mul (-(1/125:ℝ)) using 1 <;> dsimp [movingState] <;> ring
    · convert he.const_mul (8/25:ℝ) using 1
      · rfl
      · dsimp [movingState,holdInput,command,scaleState,switchingRate,switchingDisturbance]
        split_ifs <;> ring

theorem switching_rate_bounds (t : ℝ) :
    80 ≤ switchingRate t ∧ switchingRate t ≤ 120 := by
  unfold switchingRate; split_ifs <;> norm_num

theorem switching_disturbance_bound (t : ℝ) : |switchingDisturbance t| ≤ 1/100 := by
  unfold switchingDisturbance
  split_ifs with ht
  · norm_num
  · have he := (Real.exp_le_exp.mpr (show -40*t ≤ -4 by linarith)).trans exp_neg_four_le
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 4/75*Real.exp (-40*t))]
    linarith

theorem moving_initial_cube :
    ∀ i, |coordinates 0 (scaleState 10 (movingState 0)) i| ≤ 1/5000 := by
  intro i; fin_cases i <;> norm_num [movingState,coordinates,scaleState]

theorem moving_initial_exceeds_final_targets :
    |movingState 0 1| > 1/1000 ∧ |movingState 0 2| > 1/50 := by
  norm_num [movingState]

theorem inputs_really_change : switchingRate 0 ≠ switchingRate 2 ∧
    switchingDisturbance 0 ≠ switchingDisturbance 2 := by
  constructor
  · norm_num [switchingRate]
  · norm_num [switchingDisturbance]
    positivity

theorem moving_actual_certified_at_two :
    |movingState 2 1| ≤ 1/1000 ∧ |movingState 2 2| ≤ 1/50 := by
  exact two_seconds_actual_changing_input (H:=2) (c:=0) (by norm_num)
    (switching_trajectory 2) (fun t ht => (switching_rate_bounds t).1)
    (fun t ht => (switching_rate_bounds t).2)
    (fun t ht => switching_disturbance_bound t) moving_initial_cube 2 ⟨le_rfl,le_rfl⟩

/-- Existing eight-phase physical state is carried into the same hold. -/
theorem fixed_reference_then_changing_hold
    {previous : ℕ → ℝ → State} {rp wp : ℕ → ℝ → ℝ}
    (hp : DirectReference.DirectPlant previous rp wp)
    {H : ℝ} (hH : 2 ≤ H) {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 (3/5) f t+w t) f)
    (hmatch : f 0 = previous 7 (DirectReference.duration 7))
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 1/100) :
    ∀ t ∈ Icc 2 H, |f t 1| ≤ 1/1000 ∧ |f t 2| ≤ 1/50 := by
  apply two_seconds_actual_changing_input (by linarith) hf hrlo hrhi hw
  exact matched_hold_cube hmatch DirectReference.reference_endpoint
    (DirectReference.direct_cube hp 7 (by norm_num) (DirectReference.duration 7)
      ⟨(DirectReference.duration_positive 7 (by norm_num)).le,le_rfl⟩)

/-- These are exact failures of tempting weakened certificate assumptions. -/
theorem large_disturbance_breaks_certificate :
    ¬ energyRate 80 2 2 0 0 ≤ 20*(1-energy 2 0 0) := by
  norm_num [energyRate,energy]

theorem outside_rate_breaks_certificate :
    ¬ energyRate 160 (-1) (-2) 2 (-1) ≤ 20*(1-energy (-2) 2 (-1)) := by
  norm_num [energyRate,energy]

theorem initial_unit_ellipsoid_is_false : ¬ energy 16 0 0 ≤ 1 := by
  norm_num [energy]

end LeanControls.QuadraticWitness
