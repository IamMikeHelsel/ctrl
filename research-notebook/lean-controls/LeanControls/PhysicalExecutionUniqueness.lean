module
public import LeanControls.ExecutionUniqueness
public import LeanControls.PhysicalUncertainTravel

/-! Physical ODE semantics for arbitrary continuous trajectories. The controller
uses the nominal time constant `tau0`, while the plant uses its actual fixed
time constant `tau`. Both held errors are acceleration-command quantities. -/
@[expose] public section
noncomputable section
namespace LeanControls.PhysicalExecutionUniqueness
open Set SamplingClock
open UncertainLag (State)
open PhysicalTravel (normalizeState rescaleState scaleFactors normalizedDurations normalizedDisturbance)

/-- Physical equations with the trajectory's own sampled feedback. Continuity
includes every sample boundary; the ODE is imposed only between boundaries. -/
structure IsExecution (tau0 tau U : ℝ) (h e d : ℕ → ℝ) (z0 : State)
    (f : ℝ → State) : Prop where
  continuous : ContinuousOn f (Ici 0)
  initial : f 0 = z0
  ode : ∀ n, ∀ T ∈ Ioo (sampleTime h n) (sampleTime h (n+1)), ∀ i : Fin 3,
    HasDerivAt (fun S => f S i)
      (PhysicalTravel.vectorField tau
        (RobustPD.saturate U (PhysicalTravel.input tau0 (f (sampleTime h n)) + e n) + d n)
        (f T) i) T

def normalizeTrajectory (tau0 U : ℝ) (f : ℝ → State) (t : ℝ) : State :=
  normalizeState tau0 U (f (tau0*t))

theorem normalizeState_continuous (tau0 U : ℝ) : Continuous (normalizeState tau0 U) := by
  apply continuous_pi
  intro i
  exact (show Continuous (fun z : State => z i) from continuous_apply i).div_const _

theorem command_normalize {tau0 U : ℝ} (htau0 : 0 < tau0) (hU : 0 < U)
    (z : State) (e d : ℝ) :
    (RobustPD.saturate U (PhysicalTravel.input tau0 z + e) + d) / U =
      RobustPD.saturate 1 (UncertainLag.input (normalizeState tau0 U z) + e/U) + d/U := by
  have hh := PhysicalTravel.clipped_request_rescale htau0 hU (normalizeState tau0 U z) e
  rw [PhysicalTravel.rescale_normalize htau0 hU] at hh
  rw [hh, add_div]
  simp [ne_of_gt hU, UncertainLag.input]

/-- Normalization of the actual vector field, including time rescaling. -/
theorem vectorField_normalize {tau0 tau U : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (u : ℝ) (z : State) (i : Fin 3) :
    (PhysicalTravel.vectorField tau u z i * tau0) / scaleFactors tau0 U i =
      UncertainLag.vectorField (tau0/tau) (u/U) (normalizeState tau0 U z) i := by
  have ht0 : tau0 ≠ 0 := ne_of_gt htau0
  have ht : tau ≠ 0 := ne_of_gt htau
  have hu : U ≠ 0 := ne_of_gt hU
  fin_cases i <;> simp [PhysicalTravel.vectorField, UncertainLag.vectorField,
    scaleFactors, normalizeState] <;> field_simp
  ring

/-- Physical ODE and continuity assumptions imply the normalized execution
conditions. No equality to an already constructed trajectory is assumed. -/
theorem normalize_isExecution {tau0 tau U : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (h e d : ℕ → ℝ) (z0 : State)
    {f : ℝ → State} (hf : IsExecution tau0 tau U h e d z0 f) :
    ExecutionUniqueness.IsExecution (tau0/tau) (normalizedDurations tau0 h)
      (normalizedDisturbance U e) (normalizedDisturbance U d)
      (normalizeState tau0 U z0) (normalizeTrajectory tau0 U f) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (normalizeState_continuous tau0 U).comp_continuousOn
      (hf.continuous.comp (continuous_const.mul continuous_id).continuousOn
        (fun t ht => mul_nonneg htau0.le ht))
  · simp [normalizeTrajectory, hf.initial]
  · intro n t ht i
    have hT : tau0*t ∈ Ioo (sampleTime h n) (sampleTime h (n+1)) := by
      rw [PhysicalTravel.sampleTime_normalized, PhysicalTravel.sampleTime_normalized] at ht
      exact ⟨by nlinarith [(div_lt_iff₀ htau0).mp ht.1],
        by nlinarith [(lt_div_iff₀ htau0).mp ht.2]⟩
    have hsample : tau0 * sampleTime (normalizedDurations tau0 h) n = sampleTime h n := by
      rw [PhysicalTravel.sampleTime_normalized]
      field_simp
    have hd := ((hf.ode n (tau0*t) hT i).comp t
      ((hasDerivAt_id t).const_mul tau0)).div_const (scaleFactors tau0 U i)
    convert! hd using 1
    simp only [mul_one]
    rw [vectorField_normalize htau0 htau hU, command_normalize htau0 hU]
    simp [normalizeTrajectory, hsample, normalizedDisturbance]

/-- The physical specification is inhabited by the analytic execution under
positive dwell time, without requiring the uncertainty range or safety budget. -/
theorem constructed_isExecution {tau0 tau U hmin : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (hmin0 : 0 < hmin)
    (h e d : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n) :
    IsExecution tau0 tau U h e d z0 (PhysicalUncertainTravel.state tau0 tau U h e d z0) := by
  refine ⟨PhysicalUncertainTravel.state_continuousOn_nonnegative htau0 htau hmin0 h e d z0 hlo,
    PhysicalUncertainTravel.state_zero htau0 hU hmin0 h e d z0 hlo, ?_⟩
  intro n T hT i
  rw [PhysicalUncertainTravel.state_at_sample htau0 hmin0 h e d z0 hlo n]
  exact PhysicalUncertainTravel.state_ode_interior htau0 htau hU hmin0 h e d z0 hlo n hT.1 hT.2 i

/-- An arbitrary physical solution of the sampled equations equals the analytic
physical trajectory. The fixed nominal controller is not retuned to `tau`. -/
theorem execution_eq_state {tau0 tau U hmin : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (hmin0 : 0 < hmin)
    (h e d : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n)
    {f : ℝ → State} (hf : IsExecution tau0 tau U h e d z0 f) :
    EqOn f (PhysicalUncertainTravel.state tau0 tau U h e d z0) (Ici 0) := by
  have hnorm := normalize_isExecution htau0 htau hU h e d z0 hf
  have hhlo : ∀ n, hmin/tau0 ≤ normalizedDurations tau0 h n :=
    fun n => div_le_div_of_nonneg_right (hlo n) htau0.le
  have heq := ExecutionUniqueness.execution_eq_state (tau0/tau)
    (ne_of_gt (div_pos htau0 htau)) (normalizedDurations tau0 h)
    (normalizedDisturbance U e) (normalizedDisturbance U d) (normalizeState tau0 U z0)
    (div_pos hmin0 htau0) hhlo hnorm
  intro T hT
  have hh := congrArg (rescaleState tau0 U) (heq (div_nonneg hT htau0.le))
  have htime : tau0*(T/tau0) = T := by field_simp
  simpa only [normalizeTrajectory, htime, PhysicalTravel.rescale_normalize htau0 hU,
    PhysicalUncertainTravel.state] using hh

theorem execution_at_sample {tau0 tau U hmin : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (hmin0 : 0 < hmin)
    (h e d : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n)
    {f : ℝ → State} (hf : IsExecution tau0 tau U h e d z0 f) (n : ℕ) :
    f (sampleTime h n) = PhysicalUncertainTravel.samples tau0 tau U h e d z0 n := by
  have hn0 : 0 ≤ sampleTime h n :=
    (mul_nonneg (Nat.cast_nonneg n) hmin0.le).trans (sampleTime_lower h hlo n)
  rw [execution_eq_state htau0 htau hU hmin0 h e d z0 hlo hf hn0]
  exact PhysicalUncertainTravel.state_at_sample htau0 hmin0 h e d z0 hlo n

theorem execution_unique {tau0 tau U hmin : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (hmin0 : 0 < hmin)
    (h e d : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n)
    {f g : ℝ → State} (hf : IsExecution tau0 tau U h e d z0 f)
    (hg : IsExecution tau0 tau U h e d z0 g) : EqOn f g (Ici 0) := by
  intro T hT
  exact (execution_eq_state htau0 htau hU hmin0 h e d z0 hlo hf hT).trans
    (execution_eq_state htau0 htau hU hmin0 h e d z0 hlo hg hT).symm

/-- A physical travel bound for every continuous solution of the actual
held-error, sampled-feedback plant. No equality to our formula is a hypothesis. -/
theorem execution_travel_limit {tau0 tau U hmin : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (hrlo : 9/10 ≤ tau0/tau) (hrhi : tau0/tau ≤ 11/10)
    (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ tau0/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ U/100)
    (hz : TravelSafety.V (normalizeState tau0 U z0) ≤ 12)
    {f : ℝ → State} (hf : IsExecution tau0 tau U h e d z0 f) {T : ℝ} (hT : 0 ≤ T) :
    |f T 0| ≤ 2*U*tau0^2 := by
  rw [execution_eq_state htau0 htau hU hmin0 h e d z0 hlo hf hT]
  exact PhysicalUncertainTravel.travel_limit htau0 htau hU hrlo hrhi hmin0
    h e d z0 hlo hhi hbudget hz hT

end LeanControls.PhysicalExecutionUniqueness
