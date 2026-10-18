module
public import LeanControls.TravelExecution
public import LeanControls.MeasuredTravel

/-! Symbolic physical-unit interpretation of the normalized travel theorem.
The lag time constant is tau>0 and the command limit is U>0 in acceleration
units. This is an exact change of units for a specified mathematical plant;
it does not establish calibration or suitability for any particular robot. -/
@[expose] public section
noncomputable section
namespace LeanControls.PhysicalTravel
open SaturatedLag (State)
open SamplingClock

/-- Position, velocity, and acceleration units induced by tau and U. -/
def scaleFactors (tau U : ℝ) : State := ![U * tau ^ 2, U * tau, U]

def normalizeState (tau U : ℝ) (z : State) : State :=
  fun i => z i / scaleFactors tau U i

def rescaleState (tau U : ℝ) (z : State) : State :=
  fun i => scaleFactors tau U i * z i

def normalizedDurations (tau : ℝ) (h : ℕ → ℝ) : ℕ → ℝ := fun n => h n / tau

def normalizedDisturbance (U : ℝ) (w : ℕ → ℝ) : ℕ → ℝ := fun n => w n / U

/-- Physical sampled controller, with command measured in acceleration units. -/
def input (tau : ℝ) (z : State) : ℝ :=
  -z 0 / tau ^ 2 - 3 * z 1 / tau - 2 * z 2

def vectorField (tau u : ℝ) (z : State) : State :=
  ![z 1, z 2, (-z 2 + u) / tau]

def samples (tau U : ℝ) (h w : ℕ → ℝ) (z0 : State) (n : ℕ) : State :=
  rescaleState tau U (TravelSafety.samples (normalizedDurations tau h)
    (normalizedDisturbance U w) (normalizeState tau U z0) n)

/-- Physical execution at time T, obtained by an exact change of units. -/
def state (tau U : ℝ) (h w : ℕ → ℝ) (z0 : State) (T : ℝ) : State :=
  rescaleState tau U (TravelSafety.state (normalizedDurations tau h)
    (normalizedDisturbance U w) (normalizeState tau U z0) (T / tau))

/-- Physical execution with held request error before clipping and a separate
held disturbance after clipping, both in acceleration-command units. -/
def measuredState (tau U : ℝ) (h e d : ℕ → ℝ) (z0 : State) (T : ℝ) : State :=
  rescaleState tau U (MeasuredTravel.state (normalizedDurations tau h)
    (normalizedDisturbance U e) (normalizedDisturbance U d)
    (normalizeState tau U z0) (T / tau))

def measuredSamples (tau U : ℝ) (h e d : ℕ → ℝ) (z0 : State) (n : ℕ) : State :=
  rescaleState tau U (MeasuredTravel.samples (normalizedDurations tau h)
    (normalizedDisturbance U e) (normalizedDisturbance U d) (normalizeState tau U z0) n)

theorem rescale_normalize {tau U : ℝ} (htau : 0 < tau) (hU : 0 < U) (z : State) :
    rescaleState tau U (normalizeState tau U z) = z := by
  have ht : tau ≠ 0 := ne_of_gt htau
  have hu : U ≠ 0 := ne_of_gt hU
  ext i
  fin_cases i <;> simp [rescaleState, normalizeState, scaleFactors] <;> field_simp

theorem normalize_rescale {tau U : ℝ} (htau : 0 < tau) (hU : 0 < U) (z : State) :
    normalizeState tau U (rescaleState tau U z) = z := by
  have ht : tau ≠ 0 := ne_of_gt htau
  have hu : U ≠ 0 := ne_of_gt hU
  ext i
  fin_cases i <;> simp [rescaleState, normalizeState, scaleFactors, ht, hu]

theorem sampleTime_normalized (tau : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    sampleTime (normalizedDurations tau h) n = sampleTime h n / tau := by
  induction n with
  | zero => simp
  | succ n ih => simp [sampleTime_succ, ih, normalizedDurations, add_div]

theorem saturate_homogeneous {U : ℝ} (hU : 0 ≤ U) (u : ℝ) :
    RobustPD.saturate U (U * u) = U * RobustPD.saturate 1 u := by
  simp only [RobustPD.saturate, mul_max_of_nonneg _ _ hU, mul_min_of_nonneg _ _ hU]
  simp

theorem input_rescale {tau U : ℝ} (htau : 0 < tau) (z : State) :
    input tau (rescaleState tau U z) = U * SaturatedLag.input z := by
  have ht : tau ≠ 0 := ne_of_gt htau
  simp [input, rescaleState, scaleFactors, SaturatedLag.input]
  field_simp

theorem clipped_input_rescale {tau U : ℝ} (htau : 0 < tau) (hU : 0 < U) (z : State) :
    RobustPD.saturate U (input tau (rescaleState tau U z)) =
      U * RobustPD.saturate 1 (SaturatedLag.input z) := by
  rw [input_rescale htau, saturate_homogeneous hU.le]

theorem clipped_request_rescale {tau U : ℝ} (htau : 0 < tau) (hU : 0 < U)
    (z : State) (e : ℝ) :
    RobustPD.saturate U (input tau (rescaleState tau U z) + e) =
      U * RobustPD.saturate 1 (SaturatedLag.input z + e / U) := by
  have hu : U ≠ 0 := ne_of_gt hU
  rw [input_rescale htau]
  have hh : U * SaturatedLag.input z + e = U * (SaturatedLag.input z + e / U) := by
    field_simp
  rw [hh, saturate_homogeneous hU.le]

theorem state_at_sample {tau U hmin : ℝ} (htau : 0 < tau) (hmin0 : 0 < hmin)
    (h w : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    state tau U h w z0 (sampleTime h n) = samples tau U h w z0 n := by
  unfold state samples
  rw [← sampleTime_normalized]
  have hhlo : ∀ k, hmin / tau ≤ normalizedDurations tau h k :=
    fun k => div_le_div_of_nonneg_right (hlo k) htau.le
  rw [TravelSafety.state_at_sample (normalizedDurations tau h) (normalizedDisturbance U w)
    (normalizeState tau U z0) (div_pos hmin0 htau) hhlo n]

theorem state_zero {tau U hmin : ℝ} (htau : 0 < tau) (hU : 0 < U)
    (hmin0 : 0 < hmin) (h w : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n) :
    state tau U h w z0 0 = z0 := by
  have hh := state_at_sample (U := U) htau hmin0 h w z0 hlo 0
  simpa [samples, TravelSafety.samples, rescale_normalize htau hU] using hh

theorem measuredState_at_sample {tau U hmin : ℝ} (htau : 0 < tau)
    (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    measuredState tau U h e d z0 (sampleTime h n) = measuredSamples tau U h e d z0 n := by
  unfold measuredState measuredSamples
  rw [← sampleTime_normalized]
  have hhlo : ∀ k, hmin / tau ≤ normalizedDurations tau h k :=
    fun k => div_le_div_of_nonneg_right (hlo k) htau.le
  rw [MeasuredTravel.state_at_sample (normalizedDurations tau h) (normalizedDisturbance U e)
    (normalizedDisturbance U d) (normalizeState tau U z0) (div_pos hmin0 htau) hhlo n]

/-- The certified normalized ellipsoid becomes a physical position envelope.
All timings and disturbances are physical quantities in this statement. -/
theorem travel_limit {tau U hmin : ℝ} (htau : 0 < tau) (hU : 0 < U)
    (hmin0 : 0 < hmin) (h w : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ tau / 5)
    (hw : ∀ n, |w n| ≤ U / 100)
    (hz : TravelSafety.V (normalizeState tau U z0) ≤ 12) {T : ℝ} (hT : 0 ≤ T) :
    |state tau U h w z0 T 0| ≤ 2 * U * tau ^ 2 := by
  have hhlo : ∀ n, hmin / tau ≤ normalizedDurations tau h n :=
    fun n => div_le_div_of_nonneg_right (hlo n) htau.le
  have hhhi : ∀ n, normalizedDurations tau h n ≤ 1 / 5 := by
    intro n
    apply (div_le_iff₀ htau).mpr
    nlinarith [hhi n]
  have hhw : ∀ n, |normalizedDisturbance U w n| ≤ 1 / 100 := by
    intro n
    rw [normalizedDisturbance, abs_div, abs_of_pos hU]
    apply (div_le_iff₀ hU).mpr
    nlinarith [hw n]
  have hb := TravelSafety.travel_limit (normalizedDurations tau h)
    (normalizedDisturbance U w) (normalizeState tau U z0) (div_pos hmin0 htau)
    hhlo hhhi hhw hz (div_nonneg hT htau.le)
  have hs : 0 ≤ U * tau ^ 2 := mul_nonneg hU.le (sq_nonneg tau)
  change |(U * tau ^ 2) * TravelSafety.state (normalizedDurations tau h)
    (normalizedDisturbance U w) (normalizeState tau U z0) (T / tau) 0| ≤ _
  rw [abs_mul, abs_of_nonneg hs]
  nlinarith [mul_le_mul_of_nonneg_left hb hs]

/-- The physical request error and post-clamp disturbance share one certified
budget. This scales the actual measured execution, not a nominal substitute. -/
theorem measured_travel_limit {tau U hmin : ℝ} (htau : 0 < tau) (hU : 0 < U)
    (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ tau / 5)
    (hbudget : ∀ n, |e n| + |d n| ≤ U / 100)
    (hz : TravelSafety.V (normalizeState tau U z0) ≤ 12) {T : ℝ} (hT : 0 ≤ T) :
    |measuredState tau U h e d z0 T 0| ≤ 2 * U * tau ^ 2 := by
  have hhlo : ∀ n, hmin / tau ≤ normalizedDurations tau h n :=
    fun n => div_le_div_of_nonneg_right (hlo n) htau.le
  have hhhi : ∀ n, normalizedDurations tau h n ≤ 1 / 5 := by
    intro n
    apply (div_le_iff₀ htau).mpr
    nlinarith [hhi n]
  have hhb : ∀ n, |normalizedDisturbance U e n| + |normalizedDisturbance U d n| ≤
      1 / 100 := by
    intro n
    simp only [normalizedDisturbance, abs_div, abs_of_pos hU, ← add_div]
    apply (div_le_iff₀ hU).mpr
    nlinarith [hbudget n]
  have hb := MeasuredTravel.travel_limit (normalizedDurations tau h)
    (normalizedDisturbance U e) (normalizedDisturbance U d) (normalizeState tau U z0)
    (div_pos hmin0 htau) hhlo hhhi hhb hz (div_nonneg hT htau.le)
  have hs : 0 ≤ U * tau ^ 2 := mul_nonneg hU.le (sq_nonneg tau)
  change |(U * tau ^ 2) * MeasuredTravel.state (normalizedDurations tau h)
    (normalizedDisturbance U e) (normalizedDisturbance U d)
    (normalizeState tau U z0) (T / tau) 0| ≤ _
  rw [abs_mul, abs_of_nonneg hs]
  nlinarith [mul_le_mul_of_nonneg_left hb hs]

theorem vectorField_rescale {tau U : ℝ} (htau : 0 < tau) (u : ℝ) (z : State)
    (i : Fin 3) :
    scaleFactors tau U i * (ActuatorLag.vectorField u z i / tau) =
      vectorField tau (U * u) (rescaleState tau U z) i := by
  have ht : tau ≠ 0 := ne_of_gt htau
  fin_cases i <;> simp [scaleFactors, ActuatorLag.vectorField, vectorField, rescaleState]
    <;> field_simp

theorem rescaleState_continuous (tau U : ℝ) : Continuous (rescaleState tau U) := by
  apply continuous_pi
  intro i
  exact (show Continuous (fun z : State => z i) from continuous_apply i).const_mul
    (scaleFactors tau U i)

/-- The physical state also joins continuously at every sample boundary. -/
theorem state_continuousOn_nonnegative {tau U hmin : ℝ}
    (htau : 0 < tau) (hmin0 : 0 < hmin) (h w : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, hmin ≤ h n) : ContinuousOn (state tau U h w z0) (Set.Ici 0) := by
  have hhlo : ∀ k, hmin / tau ≤ normalizedDurations tau h k :=
    fun k => div_le_div_of_nonneg_right (hlo k) htau.le
  have hc := (TravelExecution.state_continuousOn_nonnegative
    (normalizedDurations tau h) (normalizedDisturbance U w) (normalizeState tau U z0)
    (div_pos hmin0 htau) hhlo).comp
    ((continuous_id.div_const tau).continuousOn)
    (fun T hT => div_nonneg hT htau.le)
  exact (rescaleState_continuous tau U).comp_continuousOn hc

theorem measuredState_continuousOn_nonnegative {tau U hmin : ℝ}
    (htau : 0 < tau) (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, hmin ≤ h n) : ContinuousOn (measuredState tau U h e d z0) (Set.Ici 0) := by
  have hhlo : ∀ k, hmin / tau ≤ normalizedDurations tau h k :=
    fun k => div_le_div_of_nonneg_right (hlo k) htau.le
  have hc := (MeasuredTravel.state_continuousOn_nonnegative
    (normalizedDurations tau h) (normalizedDisturbance U e) (normalizedDisturbance U d)
    (normalizeState tau U z0) (div_pos hmin0 htau) hhlo).comp
    ((continuous_id.div_const tau).continuousOn)
    (fun T hT => div_nonneg hT htau.le)
  exact (rescaleState_continuous tau U).comp_continuousOn hc

/-- The physical execution follows X'=V, V'=A and tau*A'=-A+u_n+w_n,
where u_n is the actual magnitude-U clamp of the sampled physical controller. -/
theorem state_ode_interior {tau U hmin : ℝ} (htau : 0 < tau) (hU : 0 < U)
    (hmin0 : 0 < hmin) (h w : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n)
    (n : ℕ) {T : ℝ} (hTlo : sampleTime h n < T) (hThi : T < sampleTime h (n + 1))
    (i : Fin 3) :
    HasDerivAt (fun R => state tau U h w z0 R i)
      (vectorField tau (RobustPD.saturate U (input tau (samples tau U h w z0 n)) + w n)
        (state tau U h w z0 T) i) T := by
  have hlo' : ∀ k, hmin / tau ≤ normalizedDurations tau h k :=
    fun k => div_le_div_of_nonneg_right (hlo k) htau.le
  have hTlo' : sampleTime (normalizedDurations tau h) n < T / tau := by
    rw [sampleTime_normalized]
    exact (div_lt_div_iff_of_pos_right htau).mpr hTlo
  have hThi' : T / tau < sampleTime (normalizedDurations tau h) (n + 1) := by
    rw [sampleTime_normalized]
    exact (div_lt_div_iff_of_pos_right htau).mpr hThi
  have hd := (TravelExecution.state_ode_interior (normalizedDurations tau h)
    (normalizedDisturbance U w) (normalizeState tau U z0) (div_pos hmin0 htau)
    hlo' n hTlo' hThi' i).comp T ((hasDerivAt_id T).div_const tau)
  have hs := hd.const_mul (scaleFactors tau U i)
  have hu : U * (RobustPD.saturate 1 (SaturatedLag.input
      (TravelSafety.samples (normalizedDurations tau h) (normalizedDisturbance U w)
        (normalizeState tau U z0) n)) + normalizedDisturbance U w n) =
      RobustPD.saturate U (input tau (samples tau U h w z0 n)) + w n := by
    rw [samples, clipped_input_rescale htau hU]
    dsimp [normalizedDisturbance]
    field_simp
  convert hs using 1
  · rfl
  · rw [← hu]
    simpa only [state, mul_one_div] using (vectorField_rescale htau
      (RobustPD.saturate 1 (SaturatedLag.input (TravelSafety.samples
        (normalizedDurations tau h) (normalizedDisturbance U w)
        (normalizeState tau U z0) n)) + normalizedDisturbance U w n)
      (TravelSafety.state (normalizedDurations tau h) (normalizedDisturbance U w)
        (normalizeState tau U z0) (T / tau)) i).symm

/-- Physical ODE for the actual measured execution: the held request error is
inside the clamp and the held disturbance is outside it. -/
theorem measuredState_ode_interior {tau U hmin : ℝ} (htau : 0 < tau) (hU : 0 < U)
    (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n)
    (n : ℕ) {T : ℝ} (hTlo : sampleTime h n < T) (hThi : T < sampleTime h (n + 1))
    (i : Fin 3) :
    HasDerivAt (fun R => measuredState tau U h e d z0 R i)
      (vectorField tau
        (RobustPD.saturate U (input tau (measuredSamples tau U h e d z0 n) + e n) + d n)
        (measuredState tau U h e d z0 T) i) T := by
  have hlo' : ∀ k, hmin / tau ≤ normalizedDurations tau h k :=
    fun k => div_le_div_of_nonneg_right (hlo k) htau.le
  have hTlo' : sampleTime (normalizedDurations tau h) n < T / tau := by
    rw [sampleTime_normalized]
    exact (div_lt_div_iff_of_pos_right htau).mpr hTlo
  have hThi' : T / tau < sampleTime (normalizedDurations tau h) (n + 1) := by
    rw [sampleTime_normalized]
    exact (div_lt_div_iff_of_pos_right htau).mpr hThi
  have hd := (MeasuredTravel.state_ode_interior (normalizedDurations tau h)
    (normalizedDisturbance U e) (normalizedDisturbance U d) (normalizeState tau U z0)
    (div_pos hmin0 htau) hlo' n hTlo' hThi' i).comp T ((hasDerivAt_id T).div_const tau)
  have hs := hd.const_mul (scaleFactors tau U i)
  have hu : U * (RobustPD.saturate 1 (SaturatedLag.input
      (MeasuredTravel.samples (normalizedDurations tau h) (normalizedDisturbance U e)
        (normalizedDisturbance U d) (normalizeState tau U z0) n) +
        normalizedDisturbance U e n) + normalizedDisturbance U d n) =
      RobustPD.saturate U (input tau (measuredSamples tau U h e d z0 n) + e n) + d n := by
    rw [measuredSamples, clipped_request_rescale htau hU]
    dsimp [normalizedDisturbance]
    field_simp
  convert hs using 1
  · rfl
  · rw [← hu]
    simpa only [measuredState, mul_one_div] using (vectorField_rescale htau
      (RobustPD.saturate 1 (SaturatedLag.input (MeasuredTravel.samples
        (normalizedDurations tau h) (normalizedDisturbance U e) (normalizedDisturbance U d)
        (normalizeState tau U z0) n) + normalizedDisturbance U e n) +
        normalizedDisturbance U d n)
      (MeasuredTravel.state (normalizedDurations tau h) (normalizedDisturbance U e)
        (normalizedDisturbance U d) (normalizeState tau U z0) (T / tau)) i).symm

/-- Illustrative units only: tau=0.1 s and U=2 m/s^2 give a 4 cm envelope,
20 ms maximum sampling interval, and 0.02 m/s^2 disturbance budget. -/
theorem illustrative_travel_limit {hmin : ℝ} (hmin0 : 0 < hmin)
    (h w : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n)
    (hhi : ∀ n, h n ≤ 1 / 50) (hw : ∀ n, |w n| ≤ 1 / 50)
    (hz : TravelSafety.V (normalizeState (1 / 10) 2 z0) ≤ 12)
    {T : ℝ} (hT : 0 ≤ T) : |state (1 / 10) 2 h w z0 T 0| ≤ 1 / 25 := by
  have hb := travel_limit (tau := 1 / 10) (U := 2) (by norm_num) (by norm_num)
    hmin0 h w z0 hlo (by intro n; norm_num; exact hhi n)
    (by intro n; norm_num; exact hw n) hz hT
  norm_num at hb ⊢
  exact hb

/-- A physical state inside that illustrative region requests twice the command
limit. This witnesses actual clipping, without claiming hardware validation. -/
theorem illustrative_active_initial :
    TravelSafety.V (normalizeState (1 / 10) 2 ![0, 0, 2]) < 12 ∧
    input (1 / 10) ![0, 0, 2] = -4 ∧
    RobustPD.saturate 2 (input (1 / 10) ![0, 0, 2]) = -2 := by
  have hn : normalizeState (1 / 10) 2 ![0, 0, 2] = ![0, 0, 1] := by
    ext i
    fin_cases i <;> norm_num [normalizeState, scaleFactors]
  rw [hn]
  refine ⟨TravelSafety.active_initial.1, ?_⟩
  norm_num [input, RobustPD.saturate]

end LeanControls.PhysicalTravel
