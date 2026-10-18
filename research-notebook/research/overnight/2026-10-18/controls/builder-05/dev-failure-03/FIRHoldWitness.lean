import FIRHold

open Set
noncomputable section
namespace RobotMotion.FIRHoldWitness
open LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.TrackingReplan LeanControls.ScaledTracking
open LeanControls.Settling LeanControls.QuadraticHold
open AccelerationAdmission FIRHold
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- A moving physical trajectory with a nonzero constant disturbance.
The constant position offset is physical, not a coordinate reset. -/
def biasedReference (b : ℝ) (t : ℝ) : State :=
  ![position 0 (1/5) (realEvents deferredReturn) t+b/800,
    velocity (1/5) (realEvents deferredReturn) t,
    acceleration (1/5) (realEvents deferredReturn) t]

/-- At rate 96/s, the controller exactly cancels the constant disturbance b.
This constructs one actual trajectory family, not existence for arbitrary inputs. -/
theorem biased_reference_trajectory (b H : ℝ) :
    IsTrajectory H (fun _ => 96)
      (fun t => physicalInput 10 (biasedReference b)
        (referenceState 0 (1/5) (realEvents deferredReturn))
        (jerk (1/5) (realEvents deferredReturn)) t+b) (biasedReference b) := by
  constructor
  · apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact ((position_continuous 0 (1/5) (realEvents deferredReturn)).add continuous_const).continuousOn
    · exact (velocity_continuous (1/5) (realEvents deferredReturn)).continuousOn
    · exact (acceleration_continuous (1/5) (realEvents deferredReturn)).continuousOn
  · intro t ht i
    fin_cases i
    · exact (position_deriv 0 (1/5) (realEvents deferredReturn) t).add_const (b/800)
    · exact velocity_deriv (1/5) (realEvents deferredReturn) t
    · convert acceleration_deriv (h:=1/5) (by norm_num) (realEvents deferredReturn) t using 1 <;>
      dsimp [biasedReference,physicalInput,referenceState] <;> ring

theorem biased_error_coordinates (b t : ℝ) (i : Fin 3) :
    coordinates 0 (scaledError 10 (biasedReference b)
      (referenceState 0 (1/5) (realEvents deferredReturn)) t) i = b/800 := by
  fin_cases i <;> dsimp [coordinates,scaledError,scaleState,error,biasedReference,referenceState] <;> ring

theorem biased_initial_cube {b : ℝ} (hb : |b| ≤ 1/100) :
    ∀ i, |coordinates 0 (scaledError 10 (biasedReference b)
      (referenceState 0 (1/5) (realEvents deferredReturn)) 0) i| ≤ 1/5000 := by
  intro i
  rw [biased_error_coordinates,abs_div]
  norm_num
  linarith

theorem biased_reference_terminal (H : ℝ) (hH : 171/50 ≤ H) :
    (∀ t ∈ Icc 0 H,
      |biasedReference (1/100) t 0-position 0 (1/5) (realEvents deferredReturn) t| ≤ 1/5000) ∧
    1/1000 ≤ biasedReference (1/100) (1/2) 0-biasedReference (1/100) 0 0 ∧
    (∀ t ∈ Icc (71/50) H, |biasedReference (1/100) t 0| ≤ 1/5000) ∧
    (∀ t ∈ Icc (171/50) H, |biasedReference (1/100) t 0| ≤ 1/5000 ∧
      |biasedReference (1/100) t 1| ≤ 1/1000 ∧ |biasedReference (1/100) t 2| ≤ 1/50) := by
  exact delayed_return_physical_terminal hH (biased_reference_trajectory (1/100) H)
    (by intro t ht; norm_num) (by intro t ht; norm_num)
    (by intro t ht; norm_num) (biased_initial_cube (by norm_num))

/-- The inherited endpoint is not zero, although the reference is zero. -/
theorem biased_endpoint_not_reset : biasedReference (1/100) (71/50) 0 = 1/80000 := by
  have hq := (deferred_return_reference_contract.2.2.2 (71/50) le_rfl).1
  norm_num [biasedReference,hq]

/-- Exact actual goal arrival does not follow from the tracking band. -/
theorem biased_terminal_not_exact_goal : biasedReference (1/100) (171/50) 0 = 1/80000 := by
  have hq := (deferred_return_reference_contract.2.2.2 (171/50) (by norm_num)).1
  norm_num [biasedReference,hq]

/-- A missing time shift cannot identify the beginning of the motion with its tail. -/
theorem wrong_clock_is_nonzero :
    position 0 (1/5) (realEvents deferredReturn) (1/2) = 779/250000 :=
  delayed_reference_progress

/-- This admissible moving witness exceeds the terminal speed before settling. -/
theorem moving_before_terminal : |biasedReference (1/100) (1/2) 1| > 1/1000 := by
  norm_num [biasedReference,velocity,response,realEvents,realEvent,deferredReturn,F1,P]

/-- No disturbance-free error reset occurs at the start either. -/
theorem initial_error_not_erased :
    coordinates 0 (scaledError 10 (biasedReference (1/100))
      (referenceState 0 (1/5) (realEvents deferredReturn)) 0) 0 = 1/80000 := by
  rw [biased_error_coordinates]
  norm_num

/-- This witness changes the actuator rate during the motion. -/
def changingRate (t : ℝ) : ℝ := if t ≤ 1/2 then 92 else 100

/-- A prescribed bounded disturbance makes the same smooth moving state solve
both rate regimes. This is a non-vacuity construction, not a disturbance model. -/
def changingDisturbance (t : ℝ) : ℝ := 1/200 +
  jerk (1/5) (realEvents deferredReturn) t * (1/changingRate t-1/96)

theorem changing_reference_trajectory (H : ℝ) :
    IsTrajectory H changingRate
      (fun t => physicalInput 10 (biasedReference (1/200))
        (referenceState 0 (1/5) (realEvents deferredReturn))
        (jerk (1/5) (realEvents deferredReturn)) t+changingDisturbance t)
      (biasedReference (1/200)) := by
  constructor
  · exact (biased_reference_trajectory (1/200) H).continuous
  · intro t ht i
    fin_cases i
    · exact (position_deriv 0 (1/5) (realEvents deferredReturn) t).add_const ((1/200)/800)
    · exact velocity_deriv (1/5) (realEvents deferredReturn) t
    · convert acceleration_deriv (h:=1/5) (by norm_num) (realEvents deferredReturn) t using 1 <;>
      dsimp [biasedReference,physicalInput,referenceState,changingDisturbance,changingRate] <;>
      (try split_ifs) <;> ring

theorem changing_rate_bounds (t : ℝ) : 80 ≤ changingRate t ∧ changingRate t ≤ 120 := by
  unfold changingRate
  split_ifs <;> norm_num

theorem changing_disturbance_bound {t : ℝ} (ht : 0 ≤ t) : |changingDisturbance t| ≤ 1/100 := by
  have hj := deferred_return_reference_contract.2.1 t ht
  have hk : |1/changingRate t-1/96| ≤ 1/2000 := by
    unfold changingRate
    split_ifs <;> norm_num
  have hb := abs_add_le (1/200:ℝ)
    (jerk (1/5) (realEvents deferredReturn) t * (1/changingRate t-1/96))
  rw [abs_mul] at hb
  have hm := mul_le_mul hj hk (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 15/2)
  dsimp [changingDisturbance]
  norm_num [one_div] at hm hb ⊢
  linarith

theorem witness_inputs_really_change : changingRate 0 ≠ changingRate 2 ∧
    changingDisturbance 0 ≠ changingDisturbance (1/2) := by
  norm_num [changingRate,changingDisturbance,jerk,eventJerk,response,realEvents,realEvent,
    deferredReturn,F3,P]

/-- The full moving witness satisfies the theorem with both inputs changing. -/
theorem changing_witness_certified (H : ℝ) (hH : 171/50 ≤ H) :
    ∀ t ∈ Icc (171/50) H, |biasedReference (1/200) t 0| ≤ 1/5000 ∧
      |biasedReference (1/200) t 1| ≤ 1/1000 ∧ |biasedReference (1/200) t 2| ≤ 1/50 := by
  exact (delayed_return_physical_terminal hH (changing_reference_trajectory H)
    (fun t ht => (changing_rate_bounds t).1) (fun t ht => (changing_rate_bounds t).2)
    (fun t ht => changing_disturbance_bound ht.1) (biased_initial_cube (by norm_num))).2.2.2

end RobotMotion.FIRHoldWitness
