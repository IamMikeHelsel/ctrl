import LeanControls.TravelSafety
import Mathlib.Tactic
noncomputable section
namespace S07CriticSource
open LeanControls Matrix
open SaturatedLag (State segment nominalSegment response)

/-- Actual source held segment, unchanged P/controller/clock/after-clamp disturbance. -/
theorem segment_eleven {t w : ℝ} (ht0 : 0≤t) (hthi : t≤1/5)
    (hw : |w|≤1/100) {z : State} (hz : TravelSafety.V z≤11) :
    TravelSafety.V (segment t z w)≤11 := by
  obtain ⟨alpha,ha0,ha1,heq⟩ := TravelSafety.region_sector z (by linarith : TravelSafety.V z≤12)
  rw [heq t w]
  apply StepScaledRobustness.matrix_invariant Generated.TravelQuarterLower.P
    Generated.TravelQuarterLower.P_psd
    (H := 1/5) (eta := 5/451) (C := 13) (W := 1/100)
    ht0 hthi (by norm_num) (by norm_num) (by linarith) (by norm_num)
    z (nominalSegment t z alpha) (w • response t) hz
  · intro ht
    subst t
    ext i
    fin_cases i <;> simp [response]
  · exact TravelSafety.nominal_contraction ht0 hthi ha0 ha1 z
  · exact TravelDisturbance.disturbance_energy_of_abs_le ht0 hthi hw

/-- The existing source recurrence, not an assumed arbitrary trajectory. -/
theorem samples_eleven (h w : ℕ → ℝ) (z0 : State)
    (hlo : ∀ n, 0≤h n) (hhi : ∀ n,h n≤1/5)
    (hw : ∀ n,|w n|≤1/100) (hz : TravelSafety.V z0≤11) :
    ∀ n, TravelSafety.V (TravelSafety.samples h w z0 n)≤11 := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih => exact segment_eleven (hlo n) (hhi n) (hw n) ih

/-- All real times use the original source clock and held-segment state. -/
theorem state_eleven (h w : ℕ → ℝ) (z0 : State) {hmin : ℝ}
    (hmin0 : 0<hmin) (hlo : ∀ n,hmin≤h n) (hhi : ∀ n,h n≤1/5)
    (hw : ∀ n,|w n|≤1/100) (hz : TravelSafety.V z0≤11)
    {t : ℝ} (ht : 0≤t) : TravelSafety.V (TravelSafety.state h w z0 t)≤11 := by
  obtain ⟨htlo,hthi⟩ := SamplingClock.segmentIndex_spec h hmin0 hlo ht
  rw [SamplingClock.sampleTime_succ] at hthi
  apply segment_eleven (sub_nonneg.mpr htlo) (by linarith [hhi (SamplingClock.segmentIndex h t)])
    (hw (SamplingClock.segmentIndex h t))
  exact samples_eleven h w z0 (fun n => hmin0.le.trans (hlo n)) hhi hw hz _

end S07CriticSource
#print axioms S07CriticSource.segment_eleven
#print axioms S07CriticSource.samples_eleven
#print axioms S07CriticSource.state_eleven
