module
public import LeanControls.UncertainLag
public import LeanControls.UncertainResponse
public import LeanControls.MeasuredTravel
public import LeanControls.StepScaledRobustness
public import LeanControls.SamplingClock

/-! Robust travel safety with a fixed controller and an unknown, fixed actuator
rate. Errors are held on each sample interval. The post-clamp error is in command
units, inside the actuator-rate factor. All statements use exact real arithmetic. -/
@[expose] public section
noncomputable section
namespace LeanControls.UncertainTravel
open Matrix BernsteinCertificate
open UncertainLag (State input heldSegment nominalSegment response)
abbrev P := Generated.TravelQuarterLower.P
abbrev V := TravelSafety.V

theorem region_sector (r : ℝ) (z : State) (hz : V z ≤ 12) :
    ∃ alpha : ℝ, 2/5 ≤ alpha ∧ alpha ≤ 1 ∧
      ∀ t w, UncertainLag.segment r t z w =
        nominalSegment r t z alpha + w • response r t := by
  apply UncertainLag.segment_sector_decomposition r z
  exact UncertainLag.tighter_sector z hz

theorem nominal_contraction {r t alpha : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (ht0 : 0 ≤ t) (hthi : t ≤ 1/5) (ha0 : 2/5 ≤ alpha) (ha1 : alpha ≤ 1)
    (z : State) :
    V (nominalSegment r t z alpha) ≤ (1 - 2*t*(15/902)) * V z := by
  have hd := UncertainLag.nominal_energy_decrease hrlo hrhi ht0 hthi ha0 ha1 z
  have hu := (Generated.TravelQuarterLower.certified_energy_bounds z).2
  norm_num [Generated.TravelQuarterLower.upperBound] at hu
  have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ t*(15/451) by positivity)
  change energy P (nominalSegment r t z alpha) ≤
    energy P z - (3/2)*t*squaredNorm z at hd
  dsimp [V, TravelSafety.V]
  nlinarith only [hd, hm]

/-- A slightly larger effective-error budget also covers converting an external
held jerk to command units at the smallest admitted rate. -/
theorem nominal_segment_invariant {r t w : ℝ}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (ht0 : 0 ≤ t) (hthi : t ≤ 1/5) (hw : |w| ≤ 1/90)
    {z : State} (hz : V z ≤ 12) : V (UncertainLag.segment r t z w) ≤ 12 := by
  obtain ⟨alpha, ha0, ha1, heq⟩ := region_sector r z hz
  rw [heq t w]
  apply StepScaledRobustness.matrix_invariant P Generated.TravelQuarterLower.P_psd
    (H := 1/5) (eta := 15/902) (C := 16) (W := 1/90)
    ht0 hthi (by norm_num) (by norm_num) (by linarith) (by norm_num)
    z (nominalSegment r t z alpha) (w • response r t) hz
  · intro ht
    subst t
    rw [UncertainLag.response_zero, smul_zero]
  · exact nominal_contraction hrlo hrhi ht0 hthi ha0 ha1 z
  · exact UncertainLag.disturbance_energy_of_abs_le hrlo hrhi ht0 hthi hw

/-- Actual command: request error before the clamp, command-equivalent error
following the clamp. The controller gains do not depend on r. -/
def segment (r t : ℝ) (z : State) (e d : ℝ) : State :=
  heldSegment r t z (RobustPD.saturate 1 (input z + e) + d)

abbrev effectiveDisturbance := MeasuredTravel.effectiveDisturbance

theorem segment_eq_effective (r t : ℝ) (z : State) (e d : ℝ) :
    segment r t z e d = UncertainLag.segment r t z (effectiveDisturbance z e d) := by
  unfold segment UncertainLag.segment effectiveDisturbance MeasuredTravel.effectiveDisturbance
  congr 1
  ring

theorem segment_zero (r : ℝ) (z : State) (e d : ℝ) : segment r 0 z e d = z :=
  UncertainLag.heldSegment_zero r z _

theorem segment_ode {r : ℝ} (hr : r ≠ 0) (t : ℝ) (z : State) (e d : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => segment r s z e d i)
      (UncertainLag.vectorField r (RobustPD.saturate 1 (input z + e) + d)
        (segment r t z e d) i) t :=
  UncertainLag.heldSegment_ode hr t z _ i

theorem segment_invariant {r t e d : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (ht0 : 0 ≤ t) (hthi : t ≤ 1/5) (hbudget : |e| + |d| ≤ 1/90)
    {z : State} (hz : V z ≤ 12) : V (segment r t z e d) ≤ 12 := by
  rw [segment_eq_effective]
  exact nominal_segment_invariant hrlo hrhi ht0 hthi
    ((MeasuredTravel.effectiveDisturbance_bound z e d).trans hbudget) hz

def samples (r : ℝ) (h e d : ℕ → ℝ) (z0 : State) : ℕ → State
  | 0 => z0
  | n+1 => segment r (h n) (samples r h e d z0 n) (e n) (d n)

theorem samples_zero (r : ℝ) (h e d : ℕ → ℝ) (z0 : State) :
    samples r h e d z0 0 = z0 := rfl

theorem samples_succ (r : ℝ) (h e d : ℕ → ℝ) (z0 : State) (n : ℕ) :
    samples r h e d z0 (n+1) = segment r (h n) (samples r h e d z0 n) (e n) (d n) := rfl

theorem samples_invariant {r : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (h e d : ℕ → ℝ) (z0 : State) (hlo : ∀ n, 0 ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1/90) (hz : V z0 ≤ 12) :
    ∀ n, V (samples r h e d z0 n) ≤ 12 := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih => exact segment_invariant hrlo hrhi (hlo n) (hhi n) (hbudget n) ih

def state (r : ℝ) (h e d : ℕ → ℝ) (z0 : State) (t : ℝ) : State :=
  let n := SamplingClock.segmentIndex h t
  segment r (t - SamplingClock.sampleTime h n) (samples r h e d z0 n) (e n) (d n)

theorem state_at_sample (r : ℝ) (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    state r h e d z0 (SamplingClock.sampleTime h n) = samples r h e d z0 n := by
  simp [state, SamplingClock.segmentIndex_at_sample h hmin0 hlo n, segment_zero]

theorem state_invariant {r : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ} (hmin0 : 0 < hmin)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1/90) (hz : V z0 ≤ 12)
    {t : ℝ} (ht : 0 ≤ t) : V (state r h e d z0 t) ≤ 12 := by
  obtain ⟨htlo, hthi⟩ := SamplingClock.segmentIndex_spec h hmin0 hlo ht
  rw [SamplingClock.sampleTime_succ] at hthi
  apply segment_invariant hrlo hrhi (sub_nonneg.mpr htlo)
    (by linarith [hhi (SamplingClock.segmentIndex h t)])
    (hbudget (SamplingClock.segmentIndex h t))
  exact samples_invariant hrlo hrhi h e d z0
    (fun n => hmin0.le.trans (hlo n)) hhi hbudget hz _

/-- For every fixed unknown rate in the interval, every admissible held
error/jitter sequence and every nonnegative real time, travel remains bounded. -/
theorem travel_limit {r : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ} (hmin0 : 0 < hmin)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1/90) (hz : V z0 ≤ 12)
    {t : ℝ} (ht : 0 ≤ t) : |state r h e d z0 t 0| ≤ 2 :=
  TravelGeometry.position_safe (state_invariant hrlo hrhi h e d z0 hmin0 hlo hhi hbudget hz ht)

/-- Original .01 combined error specification is preserved throughout the
unknown-rate interval without controller retuning. -/
theorem original_budget_travel_limit {r : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ} (hmin0 : 0 < hmin)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1/100) (hz : V z0 ≤ 12)
    {t : ℝ} (ht : 0 ≤ t) : |state r h e d z0 t 0| ≤ 2 :=
  travel_limit hrlo hrhi h e d z0 hmin0 hlo hhi
    (fun n => (hbudget n).trans (by norm_num)) hz ht

theorem active_example_travel {r t : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (ht : 0 ≤ t) : |state r (fun _ => 1/10) (fun _ => 1/200) (fun _ => 1/200)
      ![0,0,1] t 0| ≤ 2 := by
  apply original_budget_travel_limit hrlo hrhi (hmin := 1/10) _ _ _ _
    (by norm_num) (by intro n; norm_num) (by intro n; norm_num)
    (by intro n; norm_num) TravelSafety.active_initial.1.le ht

end LeanControls.UncertainTravel
