module
public import RecoveryHandoff
public import LeanControls.PhysicalExecutionUniqueness

/-! Physical-coordinate recovery semantics. `T` is the normalized handoff time,
so the physical switch occurs at `tau0*T`. The held backup command is -U;
the actual actuator uses tau, while the sampled controller retains tau0.
Both tail errors have acceleration-command units, inside the actuator lag. -/
@[expose] public section
noncomputable section
namespace LeanControls.PhysicalRecovery
open Set SamplingClock
open UncertainLag (State)
open PhysicalTravel (normalizeState rescaleState scaleFactors normalizedDurations normalizedDisturbance)
open PhysicalExecutionUniqueness (normalizeTrajectory normalizeState_continuous
  vectorField_normalize command_normalize)

/-- Actual continuous physical execution, with no assumed analytic equality or
terminal invariant. The switch does not reset any state coordinate. -/
structure IsRecoveryExecution (tau0 tau U T : ℝ) (h e d : ℕ → ℝ) (z0 : State)
    (f : ℝ → State) : Prop where
  continuous : ContinuousOn f (Ici 0)
  initial : f 0 = z0
  backup_ode : ∀ s ∈ Ioo 0 (tau0*T), ∀ i : Fin 3,
    HasDerivAt (fun q => f q i) (PhysicalTravel.vectorField tau (-U) (f s) i) s
  sampled_ode : ∀ n, ∀ s ∈ Ioo (tau0*T + sampleTime h n)
      (tau0*T + sampleTime h (n+1)), ∀ i : Fin 3,
    HasDerivAt (fun q => f q i)
      (PhysicalTravel.vectorField tau
        (RobustPD.saturate U (PhysicalTravel.input tau0
          (f (tau0*T + sampleTime h n)) + e n) + d n) (f s) i) s

/-- Physical equations imply the normalized recovery contract. In particular,
the backup -U normalizes to -1, and all tail samples use the actual trajectory. -/
theorem normalize_isRecoveryExecution {tau0 tau U T : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (h e d : ℕ → ℝ) (z0 : State)
    {f : ℝ → State} (hf : IsRecoveryExecution tau0 tau U T h e d z0 f) :
    RecoveryHandoff.IsRecoveryExecution (tau0/tau) T (normalizedDurations tau0 h)
      (normalizedDisturbance U e) (normalizedDisturbance U d)
      (normalizeState tau0 U z0) (normalizeTrajectory tau0 U f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (normalizeState_continuous tau0 U).comp_continuousOn
      (hf.continuous.comp (continuous_const.mul continuous_id).continuousOn
        (fun t ht => mul_nonneg htau0.le ht))
  · simp [normalizeTrajectory, hf.initial]
  · intro t ht i
    have hT : tau0*t ∈ Ioo 0 (tau0*T) :=
      ⟨mul_pos htau0 ht.1, mul_lt_mul_of_pos_left ht.2 htau0⟩
    have hd := ((hf.backup_ode (tau0*t) hT i).comp t
      ((hasDerivAt_id t).const_mul tau0)).div_const (scaleFactors tau0 U i)
    convert! hd using 1
    simp only [mul_one]
    rw [vectorField_normalize htau0 htau hU]
    simp [normalizeTrajectory, ne_of_gt hU]
  · intro n t ht i
    have hsample (k : ℕ) : tau0 * (T + sampleTime (normalizedDurations tau0 h) k) =
        tau0*T + sampleTime h k := by
      rw [PhysicalTravel.sampleTime_normalized]
      field_simp
    have hT : tau0*t ∈ Ioo (tau0*T + sampleTime h n)
        (tau0*T + sampleTime h (n+1)) := by
      rw [← hsample n, ← hsample (n+1)]
      exact ⟨mul_lt_mul_of_pos_left ht.1 htau0, mul_lt_mul_of_pos_left ht.2 htau0⟩
    have hd := ((hf.sampled_ode n (tau0*t) hT i).comp t
      ((hasDerivAt_id t).const_mul tau0)).div_const (scaleFactors tau0 U i)
    convert! hd using 1
    simp only [mul_one]
    rw [vectorField_normalize htau0 htau hU, command_normalize htau0 hU]
    simp [normalizeTrajectory, hsample, normalizedDisturbance]

/-- Conditional physical travel transfer. The explicit backup-path and terminal
energy obligations are evaluated in normalized coordinates for separate exact
certificates. No initial invariant is required before the recovery maneuver. -/
theorem travel_limit {tau0 tau U T hmin : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (hrlo : 9/10 ≤ tau0/tau) (hrhi : tau0/tau ≤ 11/10)
    (hT : 0 ≤ T) (hmin0 : 0 < hmin) (h e d : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ tau0/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ U/90)
    (hbackup : ∀ s ∈ Icc 0 T,
      |UncertainLag.heldSegment (tau0/tau) s (normalizeState tau0 U z0) (-1) 0| ≤ 2)
    (hterminal : UncertainTravel.V
      (UncertainLag.heldSegment (tau0/tau) T (normalizeState tau0 U z0) (-1)) ≤ 12)
    {f : ℝ → State} (hf : IsRecoveryExecution tau0 tau U T h e d z0 f)
    {s : ℝ} (hs : 0 ≤ s) : |f s 0| ≤ 2*U*tau0^2 := by
  have hhlo : ∀ n, hmin/tau0 ≤ normalizedDurations tau0 h n :=
    fun n => div_le_div_of_nonneg_right (hlo n) htau0.le
  have hhhi : ∀ n, normalizedDurations tau0 h n ≤ 1/5 := by
    intro n
    apply (div_le_iff₀ htau0).mpr
    nlinarith [hhi n]
  have hhb : ∀ n, |normalizedDisturbance U e n| + |normalizedDisturbance U d n| ≤ 1/90 := by
    intro n
    simp only [normalizedDisturbance, abs_div, abs_of_pos hU, ← add_div]
    apply (div_le_iff₀ hU).mpr
    nlinarith [hbudget n]
  have hb := RecoveryHandoff.travel_limit hrlo hrhi hT
    (normalizedDurations tau0 h) (normalizedDisturbance U e) (normalizedDisturbance U d)
    (normalizeState tau0 U z0) (div_pos hmin0 htau0) hhlo hhhi hhb hbackup hterminal
    (normalize_isRecoveryExecution htau0 htau hU h e d z0 hf) (div_nonneg hs htau0.le)
  have htime : tau0*(s/tau0) = s := by field_simp
  have hscale : 0 < U*tau0^2 := mul_pos hU (sq_pos_of_pos htau0)
  change |f (tau0*(s/tau0)) 0 / (U*tau0^2)| ≤ 2 at hb
  rw [htime, abs_div, abs_of_pos hscale] at hb
  have hh := (div_le_iff₀ hscale).mp hb
  nlinarith

/-- The physical differential-equation contract determines at most one
nonnegative-time trajectory under the same timing and held errors. -/
theorem execution_unique {tau0 tau U T hmin : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (hT : 0 ≤ T) (hmin0 : 0 < hmin)
    (h e d : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n)
    {f g : ℝ → State} (hf : IsRecoveryExecution tau0 tau U T h e d z0 f)
    (hg : IsRecoveryExecution tau0 tau U T h e d z0 g) : EqOn f g (Ici 0) := by
  have hhlo : ∀ n, hmin/tau0 ≤ normalizedDurations tau0 h n :=
    fun n => div_le_div_of_nonneg_right (hlo n) htau0.le
  have heq := RecoveryHandoff.execution_unique (ne_of_gt (div_pos htau0 htau)) hT
    (normalizedDurations tau0 h) (normalizedDisturbance U e) (normalizedDisturbance U d)
    (normalizeState tau0 U z0) (div_pos hmin0 htau0) hhlo
    (normalize_isRecoveryExecution htau0 htau hU h e d z0 hf)
    (normalize_isRecoveryExecution htau0 htau hU h e d z0 hg)
  intro s hs
  have hh := congrArg (rescaleState tau0 U) (heq (div_nonneg hs htau0.le))
  have htime : tau0*(s/tau0) = s := by field_simp
  simpa only [normalizeTrajectory, htime, PhysicalTravel.rescale_normalize htau0 hU] using hh

/-- Explicit physical execution obtained by rescaling the normalized recovery.
Its existence does not depend on the backup or terminal safety certificates. -/
def execution (tau0 tau U T : ℝ) (h e d : ℕ → ℝ) (z0 : State) (s : ℝ) : State :=
  rescaleState tau0 U (RecoveryHandoff.execution (tau0/tau) T
    (normalizedDurations tau0 h) (normalizedDisturbance U e) (normalizedDisturbance U d)
    (normalizeState tau0 U z0) (s/tau0))

/-- The physical specification has an analytic witness with no state reset.
The proof checks both rescaled ODE branches and its own physical sampled input. -/
theorem constructed_isRecoveryExecution {tau0 tau U T hmin : ℝ} (htau0 : 0 < tau0)
    (htau : 0 < tau) (hU : 0 < U) (hT : 0 ≤ T) (hmin0 : 0 < hmin)
    (h e d : ℕ → ℝ) (z0 : State) (hlo : ∀ n, hmin ≤ h n) :
    IsRecoveryExecution tau0 tau U T h e d z0 (execution tau0 tau U T h e d z0) := by
  let fn := RecoveryHandoff.execution (tau0/tau) T (normalizedDurations tau0 h)
    (normalizedDisturbance U e) (normalizedDisturbance U d) (normalizeState tau0 U z0)
  have hhlo : ∀ n, hmin/tau0 ≤ normalizedDurations tau0 h n :=
    fun n => div_le_div_of_nonneg_right (hlo n) htau0.le
  have base : RecoveryHandoff.IsRecoveryExecution (tau0/tau) T (normalizedDurations tau0 h)
      (normalizedDisturbance U e) (normalizedDisturbance U d) (normalizeState tau0 U z0) fn :=
    RecoveryHandoff.constructed_isRecoveryExecution (ne_of_gt (div_pos htau0 htau)) hT
      _ _ _ _ (div_pos hmin0 htau0) hhlo
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (PhysicalTravel.rescaleState_continuous tau0 U).comp_continuousOn
      (base.continuous.comp (continuous_id.div_const tau0).continuousOn
        (fun s hs => div_nonneg hs htau0.le))
  · change rescaleState tau0 U (fn (0/tau0)) = z0
    rw [zero_div, base.initial, PhysicalTravel.rescale_normalize htau0 hU]
  · intro s hs i
    have ht : s/tau0 ∈ Ioo 0 T :=
      ⟨div_pos hs.1 htau0, (div_lt_iff₀ htau0).mpr (by nlinarith [hs.2])⟩
    have hd := ((base.backup_ode (s/tau0) ht i).comp s
      ((hasDerivAt_id s).div_const tau0)).const_mul (scaleFactors tau0 U i)
    convert hd using 1
    · rfl
    · simpa only [execution, mul_one_div, mul_neg_one] using
        (PhysicalUncertainTravel.vectorField_rescale htau0 htau (-1) (fn (s/tau0)) i).symm
  · intro n s hs i
    have hsample (k : ℕ) : (tau0*T + sampleTime h k)/tau0 =
        T + sampleTime (normalizedDurations tau0 h) k := by
      rw [PhysicalTravel.sampleTime_normalized]
      field_simp
    have ht : s/tau0 ∈ Ioo (T + sampleTime (normalizedDurations tau0 h) n)
        (T + sampleTime (normalizedDurations tau0 h) (n+1)) := by
      rw [← hsample n, ← hsample (n+1)]
      exact ⟨(div_lt_div_iff_of_pos_right htau0).mpr hs.1,
        (div_lt_div_iff_of_pos_right htau0).mpr hs.2⟩
    have hd := ((base.sampled_ode n (s/tau0) ht i).comp s
      ((hasDerivAt_id s).div_const tau0)).const_mul (scaleFactors tau0 U i)
    have hu : U * (RobustPD.saturate 1
        (UncertainLag.input (fn (T + sampleTime (normalizedDurations tau0 h) n)) + e n/U) + d n/U) =
        RobustPD.saturate U (PhysicalTravel.input tau0
          (execution tau0 tau U T h e d z0 (tau0*T + sampleTime h n)) + e n) + d n := by
      change U * (RobustPD.saturate 1
        (UncertainLag.input (fn (T + sampleTime (normalizedDurations tau0 h) n)) + e n/U) + d n/U) =
        RobustPD.saturate U (PhysicalTravel.input tau0
          (rescaleState tau0 U (fn ((tau0*T + sampleTime h n)/tau0))) + e n) + d n
      rw [hsample, PhysicalTravel.clipped_request_rescale htau0 hU]
      dsimp [UncertainLag.input]
      field_simp
    convert hd using 1
    · rfl
    · rw [← hu]
      simpa only [execution, normalizedDisturbance, mul_one_div] using
        (PhysicalUncertainTravel.vectorField_rescale htau0 htau
          (RobustPD.saturate 1
            (UncertainLag.input (fn (T + sampleTime (normalizedDurations tau0 h) n)) + e n/U) + d n/U)
          (fn (s/tau0)) i).symm

end LeanControls.PhysicalRecovery
#print axioms LeanControls.PhysicalRecovery.normalize_isRecoveryExecution
#print axioms LeanControls.PhysicalRecovery.travel_limit
#print axioms LeanControls.PhysicalRecovery.execution_unique

#print axioms LeanControls.PhysicalRecovery.constructed_isRecoveryExecution
