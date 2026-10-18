import FIRHoldWitness

open Set
noncomputable section
namespace ControlsReview05
open LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.TrackingReplan LeanControls.ScaledTracking
open LeanControls.Settling LeanControls.QuadraticHold
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHold RobotMotion.FIRHoldWitness
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Check the stated physical controller coefficients without a unit conversion hidden in prose. -/
theorem literal_input (f q : ℝ → State) (j : ℝ → ℝ) (t : ℝ) :
    physicalInput 10 f q j t = q t 2 - 800*(f t 0-q t 0) -
      60*(f t 1-q t 1) - (f t 2-q t 2)/2 + j t/96 := by
  dsimp [physicalInput]
  ring

/-- The three initial coordinates are the claimed position-scaled errors. -/
theorem literal_cube (f q : ℝ → State) (t : ℝ) :
    coordinates 0 (scaledError 10 f q t) =
      ![f t 0-q t 0,
        f t 0-q t 0+(f t 1-q t 1)/40,
        f t 0-q t 0+(f t 1-q t 1)/20+(f t 2-q t 2)/1600] := by
  funext i
  fin_cases i <;> dsimp [coordinates,scaledError,scaleState,error] <;> ring

/-- Consume the main theorem through a literal physical command and the sole initial cube. -/
theorem literal_physical_contract {H : ℝ} (hH : 171/50 ≤ H)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t =>
      acceleration (1/5) (realEvents deferredReturn) t -
      800*(f t 0-position 0 (1/5) (realEvents deferredReturn) t) -
      60*(f t 1-velocity (1/5) (realEvents deferredReturn) t) -
      (f t 2-acceleration (1/5) (realEvents deferredReturn) t)/2 +
      jerk (1/5) (realEvents deferredReturn) t/96 + w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 1/100)
    (hi : ∀ i, |coordinates 0 (scaledError 10 f
      (referenceState 0 (1/5) (realEvents deferredReturn)) 0) i| ≤ 1/5000) :
    ∀ t ∈ Icc (171/50) H,
      |f t 0| ≤ 1/5000 ∧ |f t 1| ≤ 1/1000 ∧ |f t 2| ≤ 1/50 := by
  have same : IsTrajectory H r
      (fun t => physicalInput 10 f (referenceState 0 (1/5) (realEvents deferredReturn))
        (jerk (1/5) (realEvents deferredReturn)) t + w t) f := by
    simpa only [literal_input,referenceState,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one] using hf
  exact (delayed_return_physical_terminal hH same hrlo hrhi hw hi).2.2.2

/-- The closed terminal interval is nonempty even at the minimal horizon. -/
theorem minimal_horizon_witness :
    |biasedReference (1/200) (171/50) 0| ≤ 1/5000 ∧
    |biasedReference (1/200) (171/50) 1| ≤ 1/1000 ∧
    |biasedReference (1/200) (171/50) 2| ≤ 1/50 := by
  exact changing_witness_certified (171/50) le_rfl (171/50) ⟨le_rfl,le_rfl⟩

/-- Negative bias has the same valid trajectory and a nonzero inherited state. -/
theorem negative_bias_is_not_reset :
    biasedReference (-1/100) (71/50) = ![-1/80000,0,0] := by
  simpa using biased_tail_state (-1/100) (71/50) le_rfl

/-- A wrong input clock is not an actual trajectory, despite preserving its state curve. -/
theorem wrong_clock_is_not_trajectory :
    ¬ IsTrajectory 2 changingRate
      (fun s => holdInput 10 0 (fun u => biasedReference (1/200) (71/50+u)) s +
        changingDisturbance s)
      (fun s => biasedReference (1/200) (71/50+s)) := by
  intro hbad
  have hd := hbad.ode (1/2) (by norm_num) 2
  change HasDerivAt (fun s => biasedReference (1/200) (71/50+s) 2)
    wrongClockRHS (1/2) at hd
  rw [wrong_clock_rhs_nonzero] at hd
  have hc := (trajectory_shift (t0:=71/50) (by norm_num)
    (changing_reference_trajectory 4)).ode (1/2) (by norm_num) 2
  have hzero : HasDerivAt (fun s => biasedReference (1/200) (71/50+s) 2) 0 (1/2) := by
    convert hc using 1 <;>
      norm_num [biasedReference,physicalInput,referenceState,changingRate,changingDisturbance,
        position,velocity,acceleration,jerk,eventJerk,response,realEvents,realEvent,
        deferredReturn,F0,F1,F2,F3,P,RobotMotion.H]
  have impossible := hzero.unique hd
  norm_num at impossible

/-- With no initial cube, a valid hold trajectory can violate the late speed band. -/
def largeInitial (t : ℝ) : State :=
  ![Real.exp (-40*(t-2)), -40*Real.exp (-40*(t-2)), 1600*Real.exp (-40*(t-2))]

theorem large_initial_is_actual (H : ℝ) :
    IsTrajectory H (fun _ => 80) (fun t => holdInput 10 0 largeInitial t) largeInitial := by
  constructor
  · unfold largeInitial
    fun_prop
  · intro t ht i
    have he : HasDerivAt (fun s : ℝ => Real.exp (-40*(s-2)))
        (Real.exp (-40*(t-2)) * (-40)) t := by
      convert (((hasDerivAt_id t).sub_const 2).const_mul (-40)).exp using 1 <;> ring
    fin_cases i
    · convert he using 1 <;> dsimp [largeInitial] <;> ring
    · convert he.const_mul (-40) using 1 <;> dsimp [largeInitial] <;> ring
    · convert he.const_mul 1600 using 1 <;>
        dsimp [largeInitial,holdInput,command,scaleState] <;> ring

theorem large_initial_violates_terminal_speed : |largeInitial 2 1| > 1/1000 := by
  norm_num [largeInitial]

theorem large_initial_violates_terminal_acceleration : |largeInitial 2 2| > 1/50 := by
  norm_num [largeInitial]

/-- An independent full FIR witness retains a nonzero exponential physical error. -/
def residualMotion (t : ℝ) : State :=
  ![position 0 (1/5) (realEvents deferredReturn) t + Real.exp (-80*t)/5000,
    velocity (1/5) (realEvents deferredReturn) t - (2/125)*Real.exp (-80*t),
    acceleration (1/5) (realEvents deferredReturn) t + (32/25)*Real.exp (-80*t)]

def residualDisturbance (t : ℝ) : ℝ := jerk (1/5) (realEvents deferredReturn) t/1920

theorem residual_motion_is_actual (H : ℝ) :
    IsTrajectory H (fun _ => 640/7)
      (fun t => physicalInput 10 residualMotion
        (referenceState 0 (1/5) (realEvents deferredReturn))
        (jerk (1/5) (realEvents deferredReturn)) t+residualDisturbance t) residualMotion := by
  constructor
  · have hp := position_continuous 0 (1/5) (realEvents deferredReturn)
    have hv := velocity_continuous (1/5) (realEvents deferredReturn)
    have ha := acceleration_continuous (1/5) (realEvents deferredReturn)
    apply continuousOn_pi.mpr
    intro i
    fin_cases i <;> dsimp [residualMotion] <;> fun_prop
  · intro t ht i
    have he := (((hasDerivAt_id t).const_mul (-80:ℝ)).exp)
    fin_cases i
    · convert (position_deriv 0 (1/5) (realEvents deferredReturn) t).add
        (he.div_const 5000) using 1 <;> dsimp [residualMotion] <;> ring
    · convert (velocity_deriv (1/5) (realEvents deferredReturn) t).sub
        (he.const_mul (2/125)) using 1 <;> dsimp [residualMotion] <;> ring
    · convert (acceleration_deriv (h:=1/5) (by norm_num) (realEvents deferredReturn) t).add
        (he.const_mul (32/25)) using 1 <;>
        dsimp [residualMotion,physicalInput,referenceState,residualDisturbance] <;> ring

theorem residual_initial_cube :
    ∀ i, |coordinates 0 (scaledError 10 residualMotion
      (referenceState 0 (1/5) (realEvents deferredReturn)) 0) i| ≤ 1/5000 := by
  intro i
  fin_cases i <;> norm_num [residualMotion,coordinates,scaledError,scaleState,error,
    referenceState,position,velocity,acceleration,response,realEvents,realEvent,
    deferredReturn,F0,F1,F2,P]

theorem residual_disturbance_bound {t : ℝ} (ht : 0 ≤ t) : |residualDisturbance t| ≤ 1/100 := by
  have hj := deferred_return_reference_contract.2.1 t ht
  dsimp [residualDisturbance]
  rw [abs_div]
  norm_num
  linarith

theorem residual_motion_certified :
    ∀ t ∈ Icc (171/50:ℝ) 4,
      |residualMotion t 0| ≤ 1/5000 ∧
      |residualMotion t 1| ≤ 1/1000 ∧ |residualMotion t 2| ≤ 1/50 := by
  exact (delayed_return_physical_terminal (H:=4) (by norm_num)
    (residual_motion_is_actual 4) (by intro t ht; norm_num)
    (by intro t ht; norm_num) (fun t ht => residual_disturbance_bound ht.1)
    residual_initial_cube).2.2.2

/-- The proved terminal bands do not imply exact finite-time rest. -/
theorem residual_terminal_speed_nonzero : residualMotion (171/50) 1 ≠ 0 := by
  have hv := (deferred_return_reference_contract.2.2.2 (171/50) (by norm_num)).2.1
  dsimp [residualMotion]
  rw [hv]
  have hp := Real.exp_pos (-80*(171/50:ℝ))
  nlinarith

/-- The two-second local hold begins at global 1.42, hence global 3.42. -/
theorem timing_gap : (71/50:ℝ)+2 = 171/50 ∧ (17/10:ℝ) < 171/50 ∧ (13/10:ℝ) < 71/50 := by
  norm_num

end ControlsReview05
