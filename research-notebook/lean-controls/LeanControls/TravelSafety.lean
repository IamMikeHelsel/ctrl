module
public import LeanControls.SaturatedLag
public import LeanControls.TravelGeometry
public import LeanControls.TravelDisturbance
public import LeanControls.StepScaledRobustness
public import LeanControls.SamplingClock

/-! A region-wide, all-real-time travel guarantee for a normalized saturated
actuator-lag axis. Disturbance is constant on each interval, enters after the
command clamp, and may change arbitrarily at sample boundaries. No machine
arithmetic, parameter uncertainty, or physical calibration is asserted. -/
@[expose] public section
noncomputable section
namespace LeanControls.TravelSafety
open Matrix BernsteinCertificate
open SaturatedLag (State input segment nominalSegment response segment_zero segment_sector_decomposition nominal_energy_decrease)
abbrev P := Generated.TravelQuarterLower.P

def V (z : State) : ℝ := energy P z

/-- The whole certified region admits a fixed-per-segment sector gain. -/
theorem region_sector (z : State) (hz : V z ≤ 12) :
    ∃ alpha : ℝ, 1 / 4 ≤ alpha ∧ alpha ≤ 1 ∧
      ∀ t w, segment t z w = nominalSegment t z alpha + w • response t := by
  apply segment_sector_decomposition z
  have hs := TravelGeometry.sector_safe hz
  change (1/4:ℝ) * |input z| ≤ 1 at hs
  linarith

/-- Contraction for every elapsed time and every admitted frozen gain. -/
theorem nominal_contraction {t alpha : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1/5)
    (ha0 : 1/4 ≤ alpha) (ha1 : alpha ≤ 1) (z : State) :
    V (nominalSegment t z alpha) ≤ (1 - 2*t*(5/451)) * V z := by
  have hd := nominal_energy_decrease ht0 hthi ha0 ha1 z
  have hu := (Generated.TravelQuarterLower.certified_energy_bounds z).2
  norm_num [Generated.TravelQuarterLower.upperBound] at hu
  have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ t*(10/451) by positivity)
  change energy P (nominalSegment t z alpha) ≤ energy P z - t * squaredNorm z at hd
  dsimp [V]
  nlinarith only [hd, hm]

/-- Every point of a held segment remains in the same ellipsoid. The additive
budget scales with elapsed time, so this also covers arbitrarily small times. -/
theorem segment_invariant {t w : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1/5)
    (hw : |w| ≤ 1/100) {z : State} (hz : V z ≤ 12) :
    V (segment t z w) ≤ 12 := by
  obtain ⟨alpha, ha0, ha1, heq⟩ := region_sector z hz
  rw [heq t w]
  apply StepScaledRobustness.matrix_invariant P Generated.TravelQuarterLower.P_psd
    (H := 1/5) (eta := 5/451) (C := 13) (W := 1/100)
    ht0 hthi (by norm_num) (by norm_num) (by linarith) (by norm_num)
    z (nominalSegment t z alpha) (w • response t) hz
  · intro ht
    subst t
    ext i
    fin_cases i <;> simp [response]
  · exact nominal_contraction ht0 hthi ha0 ha1 z
  · exact TravelDisturbance.disturbance_energy_of_abs_le ht0 hthi hw

/-- Travel is bounded throughout each held interval, not merely at samples. -/
theorem segment_position_safe {t w : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1/5)
    (hw : |w| ≤ 1/100) {z : State} (hz : V z ≤ 12) :
    |segment t z w 0| ≤ 2 :=
  TravelGeometry.position_safe (segment_invariant ht0 hthi hw hz)

/-- Defined sampled execution; the recurrence is not an unproved feasibility assumption. -/
def samples (h w : ℕ → ℝ) (z0 : State) : ℕ → State
  | 0 => z0
  | n+1 => segment (h n) (samples h w z0 n) (w n)

theorem samples_zero (h w : ℕ → ℝ) (z0 : State) : samples h w z0 0 = z0 := rfl

theorem samples_succ (h w : ℕ → ℝ) (z0 : State) (n : ℕ) :
    samples h w z0 (n+1) = segment (h n) (samples h w z0 n) (w n) := rfl

theorem samples_invariant (h w : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, 0 ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hw : ∀ n, |w n| ≤ 1/100) (hz : V z0 ≤ 12) :
    ∀ n, V (samples h w z0 n) ≤ 12 := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih => exact segment_invariant (hlo n) (hhi n) (hw n) ih

/-- Clock assembly evaluates the exact held solution on the containing interval. -/
def state (h w : ℕ → ℝ) (z0 : State) (t : ℝ) : State :=
  let n := SamplingClock.segmentIndex h t
  segment (t - SamplingClock.sampleTime h n) (samples h w z0 n) (w n)

theorem state_at_sample (h w : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (n : ℕ) :
    state h w z0 (SamplingClock.sampleTime h n) = samples h w z0 n := by
  simp [state, SamplingClock.segmentIndex_at_sample h hmin0 hlo n, segment_zero]

/-- Positive minimum dwell time ensures coverage of every finite real time. -/
theorem state_invariant (h w : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hw : ∀ n, |w n| ≤ 1/100) (hz : V z0 ≤ 12) {t : ℝ} (ht : 0 ≤ t) :
    V (state h w z0 t) ≤ 12 := by
  obtain ⟨htlo, hthi⟩ := SamplingClock.segmentIndex_spec h hmin0 hlo ht
  rw [SamplingClock.sampleTime_succ] at hthi
  apply segment_invariant (sub_nonneg.mpr htlo) (by linarith [hhi (SamplingClock.segmentIndex h t)])
    (hw (SamplingClock.segmentIndex h t))
  exact samples_invariant h w z0 (fun n => hmin0.le.trans (hlo n)) hhi hw hz _

/-- Main safety statement: every admissible initial state, every jitter sequence,
every bounded held disturbance sequence, and every nonnegative real time. -/
theorem travel_limit (h w : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hw : ∀ n, |w n| ≤ 1/100) (hz : V z0 ≤ 12) {t : ℝ} (ht : 0 ≤ t) :
    |state h w z0 t 0| ≤ 2 :=
  TravelGeometry.position_safe (state_invariant h w z0 hmin0 hlo hhi hw hz ht)

/-- A nonzero initial state strictly inside the region requests twice the limit. -/
theorem active_initial : V ![0,0,1] < 12 ∧ input ![0,0,1] = -2 ∧
    RobustPD.saturate 1 (input ![0,0,1]) = -1 := by
  refine ⟨?_, ?_, ?_⟩
  · change energy P ![0,0,1] < 12
    rw [TravelGeometry.active_initial_energy]
    norm_num
  · norm_num [input]
  · norm_num [input, RobustPD.saturate]

/-- The active-clipping witness enjoys the same universal jitter/disturbance guarantee. -/
theorem active_initial_travel (h w : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hw : ∀ n, |w n| ≤ 1/100) {t : ℝ} (ht : 0 ≤ t) :
    |state h w ![0,0,1] t 0| ≤ 2 :=
  travel_limit h w ![0,0,1] hmin0 hlo hhi hw active_initial.1.le ht

end LeanControls.TravelSafety
