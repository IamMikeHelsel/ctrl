import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- Isolated S12 abstraction experiment. The box is for decision objectives only.
   The incompatible point is a hypothetical joint readout of (w,b=w+d), NOT
   the original scalar heldout row or an observed physical measurement. -/
set_option autoImplicit false
namespace S12DecisionBox

theorem proposed_point_inside_marginal_box :
    (27 / 70 : ℝ) ≤ 27 / 70 ∧ (27 / 70 : ℝ) ≤ 47 / 80 ∧
    (9 / 10 : ℝ) ≤ 9 / 10 ∧ (9 / 10 : ℝ) ≤ 11 / 10 := by
  norm_num

theorem proposed_point_has_no_original_world (d q leakage : ℝ)
    (baseline_readout : (27 / 70 : ℝ) + d = 9 / 10)
    (leakage_high : leakage ≤ 3 / 10)
    (shared_leakage : q = leakage * d)
    (separating_low : (3 / 5 : ℝ) ≤ 27 / 70 + q) : False := by
  have hd : d = 18 / 35 := by linarith
  have hq : q ≤ 27 / 175 := by nlinarith
  linarith

theorem interval_absolute_bound (lo hi x correction limit : ℝ)
    (hlo : lo ≤ x) (hhi : x ≤ hi)
    (left : |lo + correction| ≤ limit) (right : |hi + correction| ≤ limit) :
    |x + correction| ≤ limit := by
  obtain ⟨hll, hlu⟩ := abs_le.mp left
  obtain ⟨hrl, hru⟩ := abs_le.mp right
  apply abs_le.mpr
  constructor <;> linarith

theorem response_coordinate_identity (w d b correction rho : ℝ) (hb : b = w + d) :
    w + correction + rho * d =
      (1 - rho) * (w + correction) + rho * (b + correction) := by
  rw [hb]
  ring

theorem uncertain_response_iff_endpoint_bounds (w b correction limit : ℝ) :
    (∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      |(1 - rho) * (w + correction) + rho * (b + correction)| ≤ limit) ↔
    (|w + correction| ≤ limit ∧ |b + correction| ≤ limit) := by
  constructor
  · intro h
    constructor
    · simpa using h 0 (by norm_num) (by norm_num)
    · simpa using h 1 (by norm_num) (by norm_num)
  · rintro ⟨hw, hb⟩ rho hrlo hrhi
    obtain ⟨hwl, hwu⟩ := abs_le.mp hw
    obtain ⟨hbl, hbu⟩ := abs_le.mp hb
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg hrlo (show 0 ≤ b + correction + limit by linarith),
        mul_nonneg (show 0 ≤ 1 - rho by linarith)
          (show 0 ≤ w + correction + limit by linarith)]
    · nlinarith [mul_nonneg hrlo (show 0 ≤ limit - (b + correction) by linarith),
        mul_nonneg (show 0 ≤ 1 - rho by linarith)
          (show 0 ≤ limit - (w + correction) by linarith)]

theorem decision_box_lossless_for_endpoint_objectives
    (world : ℝ → ℝ → Prop) (wl wu bl bu correction wheelLimit mixedLimit : ℝ)
    (contained : ∀ w b, world w b → wl ≤ w ∧ w ≤ wu ∧ bl ≤ b ∧ b ≤ bu)
    (wheel_low_attained : ∃ b, world wl b)
    (wheel_high_attained : ∃ b, world wu b)
    (baseline_low_attained : ∃ w, world w bl)
    (baseline_high_attained : ∃ w, world w bu) :
    (∀ w b, world w b → |w + correction| ≤ wheelLimit ∧
      |w + correction| ≤ mixedLimit ∧ |b + correction| ≤ mixedLimit) ↔
    (∀ w b, wl ≤ w → w ≤ wu → bl ≤ b → b ≤ bu →
      |w + correction| ≤ wheelLimit ∧
      |w + correction| ≤ mixedLimit ∧ |b + correction| ≤ mixedLimit) := by
  constructor
  · intro h w b hwlo hwhi hblo hbhi
    rcases wheel_low_attained with ⟨bwlo, hwlo_world⟩
    rcases wheel_high_attained with ⟨bwhi, hwhi_world⟩
    rcases baseline_low_attained with ⟨wblo, hblo_world⟩
    rcases baseline_high_attained with ⟨wbhi, hbhi_world⟩
    have hlo := h wl bwlo hwlo_world
    have hhi := h wu bwhi hwhi_world
    have hb_low := h wblo bl hblo_world
    have hb_high := h wbhi bu hbhi_world
    exact ⟨interval_absolute_bound wl wu w correction wheelLimit hwlo hwhi hlo.1 hhi.1,
      interval_absolute_bound wl wu w correction mixedLimit hwlo hwhi hlo.2.1 hhi.2.1,
      interval_absolute_bound bl bu b correction mixedLimit hblo hbhi hb_low.2.2 hb_high.2.2⟩
  · intro h w b hw
    obtain ⟨hwlo, hwhi, hblo, hbhi⟩ := contained w b hw
    exact h w b hwlo hwhi hblo hbhi

#print axioms proposed_point_inside_marginal_box
#print axioms proposed_point_has_no_original_world
#print axioms interval_absolute_bound
#print axioms response_coordinate_identity
#print axioms uncertain_response_iff_endpoint_bounds
#print axioms decision_box_lossless_for_endpoint_objectives
end S12DecisionBox
