module
public import LeanControls.PhysicalTravel
public import LeanControls.UncertainExecution

/-! Physical interpretation of a fixed nominal controller with uncertain actual
actuator time constant. State and time normalization use `tau0` throughout;
the physical plant uses `tau`, yielding normalized rate `tau0 / tau`.
Both held errors are in acceleration-command units. This is a conditional
mathematical model, not a calibration or hardware-validation claim. -/
@[expose] public section
noncomputable section
namespace LeanControls.PhysicalUncertainTravel
open SaturatedLag (State)
open SamplingClock
open PhysicalTravel (scaleFactors normalizeState rescaleState normalizedDurations
  normalizedDisturbance input vectorField)

/-- Samples of the actual uncertain plant under the fixed nominal controller. -/
def samples (tau0 tau U : ℝ) (h e d : ℕ → ℝ) (z0 : State) (n : ℕ) : State :=
  rescaleState tau0 U (UncertainTravel.samples (tau0 / tau)
    (normalizedDurations tau0 h) (normalizedDisturbance U e)
    (normalizedDisturbance U d) (normalizeState tau0 U z0) n)

/-- Physical trajectory. Changing `tau` leaves the normalization and controller
at the same nominal `tau0`; only the actual plant rate changes. -/
def state (tau0 tau U : ℝ) (h e d : ℕ → ℝ) (z0 : State) (T : ℝ) : State :=
  rescaleState tau0 U (UncertainTravel.state (tau0 / tau)
    (normalizedDurations tau0 h) (normalizedDisturbance U e)
    (normalizedDisturbance U d) (normalizeState tau0 U z0) (T / tau0))

theorem samples_zero {tau0 tau U : ℝ} (htau0 : 0 < tau0) (hU : 0 < U)
    (h e d : ℕ → ℝ) (z0 : State) : samples tau0 tau U h e d z0 0 = z0 := by
  simp [samples, UncertainTravel.samples_zero, PhysicalTravel.rescale_normalize htau0 hU]

theorem state_at_sample {tau0 tau U hmin : ℝ} (htau0 : 0 < tau0)
    (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    state tau0 tau U h e d z0 (sampleTime h n) = samples tau0 tau U h e d z0 n := by
  unfold state samples
  rw [← PhysicalTravel.sampleTime_normalized]
  have hhlo : ∀ k, hmin / tau0 ≤ normalizedDurations tau0 h k :=
    fun k => div_le_div_of_nonneg_right (hlo k) htau0.le
  rw [UncertainTravel.state_at_sample (tau0 / tau) (normalizedDurations tau0 h)
    (normalizedDisturbance U e) (normalizedDisturbance U d) (normalizeState tau0 U z0)
    (div_pos hmin0 htau0) hhlo n]

theorem state_zero {tau0 tau U hmin : ℝ} (htau0 : 0 < tau0) (hU : 0 < U)
    (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, hmin ≤ h n) : state tau0 tau U h e d z0 0 = z0 := by
  have hh := state_at_sample (tau := tau) (U := U) htau0 hmin0 h e d z0 hlo 0
  simpa only [sampleTime_zero, samples_zero htau0 hU] using hh

/-- The physical envelope uses the fixed nominal time constant. The actual
plant may have any fixed positive time constant in the certified rate interval. -/
theorem travel_limit {tau0 tau U hmin : ℝ} (htau0 : 0 < tau0) (_htau : 0 < tau)
    (hU : 0 < U) (hrlo : 9 / 10 ≤ tau0 / tau) (hrhi : tau0 / tau ≤ 11 / 10)
    (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ tau0 / 5)
    (hbudget : ∀ n, |e n| + |d n| ≤ U / 100)
    (hz : TravelSafety.V (normalizeState tau0 U z0) ≤ 12) {T : ℝ} (hT : 0 ≤ T) :
    |state tau0 tau U h e d z0 T 0| ≤ 2 * U * tau0 ^ 2 := by
  have hhlo : ∀ n, hmin / tau0 ≤ normalizedDurations tau0 h n :=
    fun n => div_le_div_of_nonneg_right (hlo n) htau0.le
  have hhhi : ∀ n, normalizedDurations tau0 h n ≤ 1 / 5 := by
    intro n
    apply (div_le_iff₀ htau0).mpr
    nlinarith [hhi n]
  have hhb : ∀ n, |normalizedDisturbance U e n| + |normalizedDisturbance U d n| ≤
      1 / 100 := by
    intro n
    simp only [normalizedDisturbance, abs_div, abs_of_pos hU, ← add_div]
    apply (div_le_iff₀ hU).mpr
    nlinarith [hbudget n]
  have hb := UncertainTravel.original_budget_travel_limit hrlo hrhi
    (normalizedDurations tau0 h) (normalizedDisturbance U e) (normalizedDisturbance U d)
    (normalizeState tau0 U z0) (div_pos hmin0 htau0) hhlo hhhi hhb hz
    (div_nonneg hT htau0.le)
  have hs : 0 ≤ U * tau0 ^ 2 := mul_nonneg hU.le (sq_nonneg tau0)
  change |(U * tau0 ^ 2) * UncertainTravel.state (tau0 / tau)
    (normalizedDurations tau0 h) (normalizedDisturbance U e) (normalizedDisturbance U d)
    (normalizeState tau0 U z0) (T / tau0) 0| ≤ _
  rw [abs_mul, abs_of_nonneg hs]
  nlinarith [mul_le_mul_of_nonneg_left hb hs]

/-- The rate interval corresponds to this asymmetric actual-time-constant
interval relative to the fixed nominal constant. -/
theorem time_constant_interval {tau0 tau : ℝ} (htau0 : 0 < tau0) (htau : 0 < tau)
    (hrlo : 9 / 10 ≤ tau0 / tau) (hrhi : tau0 / tau ≤ 11 / 10) :
    10 / 11 ≤ tau / tau0 ∧ tau / tau0 ≤ 10 / 9 := by
  constructor
  · apply (le_div_iff₀ htau0).mpr
    have h := (div_le_iff₀ htau).mp hrhi
    nlinarith
  · apply (div_le_iff₀ htau0).mpr
    have h := (le_div_iff₀ htau).mp hrlo
    nlinarith

/-- The physical derivative retains the actual lag `tau`; it is not replaced
by the nominal normalization constant `tau0`. -/
theorem vectorField_rescale {tau0 tau U : ℝ} (htau0 : 0 < tau0) (htau : 0 < tau)
    (u : ℝ) (z : State) (i : Fin 3) :
    scaleFactors tau0 U i * (UncertainLag.vectorField (tau0 / tau) u z i / tau0) =
      vectorField tau (U * u) (rescaleState tau0 U z) i := by
  have ht0 : tau0 ≠ 0 := ne_of_gt htau0
  have ht : tau ≠ 0 := ne_of_gt htau
  fin_cases i <;>
    simp [scaleFactors, UncertainLag.vectorField, vectorField, rescaleState] <;>
    field_simp <;> ring

/-- Continuity includes all sample boundaries despite changes in held errors. -/
theorem state_continuousOn_nonnegative {tau0 tau U hmin : ℝ}
    (htau0 : 0 < tau0) (htau : 0 < tau) (hmin0 : 0 < hmin)
    (h e d : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n) :
    ContinuousOn (state tau0 tau U h e d z0) (Set.Ici 0) := by
  have hhlo : ∀ k, hmin / tau0 ≤ normalizedDurations tau0 h k :=
    fun k => div_le_div_of_nonneg_right (hlo k) htau0.le
  have hc := (UncertainExecution.state_continuousOn_nonnegative
    (tau0 / tau) (ne_of_gt (div_pos htau0 htau)) (normalizedDurations tau0 h)
    (normalizedDisturbance U e) (normalizedDisturbance U d) (normalizeState tau0 U z0)
    (div_pos hmin0 htau0) hhlo).comp
    ((continuous_id.div_const tau0).continuousOn)
    (fun T hT => div_nonneg hT htau0.le)
  exact (PhysicalTravel.rescaleState_continuous tau0 U).comp_continuousOn hc

/-- Exact physical ODE on every sampling-interval interior. The feedback uses
`tau0`, whereas the physical acceleration dynamics use the actual `tau`:
X'=V, V'=A, tau*A'=-A+clip_U(input_tau0(sample)+e_n)+d_n. -/
theorem state_ode_interior {tau0 tau U hmin : ℝ} (htau0 : 0 < tau0) (htau : 0 < tau)
    (hU : 0 < U) (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, hmin ≤ h n) (n : ℕ) {T : ℝ}
    (hTlo : sampleTime h n < T) (hThi : T < sampleTime h (n + 1)) (i : Fin 3) :
    HasDerivAt (fun R => state tau0 tau U h e d z0 R i)
      (vectorField tau
        (RobustPD.saturate U (input tau0 (samples tau0 tau U h e d z0 n) + e n) + d n)
        (state tau0 tau U h e d z0 T) i) T := by
  have hlo' : ∀ k, hmin / tau0 ≤ normalizedDurations tau0 h k :=
    fun k => div_le_div_of_nonneg_right (hlo k) htau0.le
  have hTlo' : sampleTime (normalizedDurations tau0 h) n < T / tau0 := by
    rw [PhysicalTravel.sampleTime_normalized]
    exact (div_lt_div_iff_of_pos_right htau0).mpr hTlo
  have hThi' : T / tau0 < sampleTime (normalizedDurations tau0 h) (n + 1) := by
    rw [PhysicalTravel.sampleTime_normalized]
    exact (div_lt_div_iff_of_pos_right htau0).mpr hThi
  have hd := (UncertainExecution.state_ode_interior (tau0 / tau)
    (ne_of_gt (div_pos htau0 htau)) (normalizedDurations tau0 h)
    (normalizedDisturbance U e) (normalizedDisturbance U d) (normalizeState tau0 U z0)
    (div_pos hmin0 htau0) hlo' n hTlo' hThi' i).comp T
    ((hasDerivAt_id T).div_const tau0)
  have hs := hd.const_mul (scaleFactors tau0 U i)
  have hu : U * (RobustPD.saturate 1 (SaturatedLag.input
      (UncertainTravel.samples (tau0 / tau) (normalizedDurations tau0 h)
        (normalizedDisturbance U e) (normalizedDisturbance U d)
        (normalizeState tau0 U z0) n) + normalizedDisturbance U e n) +
        normalizedDisturbance U d n) =
      RobustPD.saturate U (input tau0 (samples tau0 tau U h e d z0 n) + e n) + d n := by
    rw [samples, PhysicalTravel.clipped_request_rescale htau0 hU]
    dsimp [normalizedDisturbance]
    field_simp
  convert hs using 1
  · rfl
  · rw [← hu]
    simpa only [state, mul_one_div] using (vectorField_rescale htau0 htau
      (RobustPD.saturate 1 (SaturatedLag.input (UncertainTravel.samples (tau0 / tau)
        (normalizedDurations tau0 h) (normalizedDisturbance U e) (normalizedDisturbance U d)
        (normalizeState tau0 U z0) n) + normalizedDisturbance U e n) +
        normalizedDisturbance U d n)
      (UncertainTravel.state (tau0 / tau) (normalizedDurations tau0 h)
        (normalizedDisturbance U e) (normalizedDisturbance U d)
        (normalizeState tau0 U z0) (T / tau0)) i).symm

end LeanControls.PhysicalUncertainTravel
