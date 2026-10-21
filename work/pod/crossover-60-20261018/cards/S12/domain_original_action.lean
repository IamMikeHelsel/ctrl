import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- Original source-attribution static scalar contract; no prior is changed.
   AI-written isolated research statement, not an approved Challenge solution.
   Theorem is over real worlds, with the exact common leakage equation. -/
set_option autoImplicit false
namespace S12OriginalAction

theorem original_wheel_range (w d q leakage : ℝ)
    (leakage_low : 1 / 5 ≤ leakage) (leakage_high : leakage ≤ 3 / 10)
    (shared_leakage : q = leakage * d)
    (baseline_low : 9 / 10 ≤ w + d) (baseline_high : w + d ≤ 11 / 10)
    (separating_low : 3 / 5 ≤ w + q) (separating_high : w + q ≤ 13 / 20) :
    27 / 70 ≤ w ∧ w ≤ 47 / 80 := by
  have hd : 0 ≤ d := by
    by_contra hn
    have hdn : d ≤ 0 := le_of_lt (lt_of_not_ge hn)
    have hprod : (1 - leakage) * d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hdn
    nlinarith
  have hqlo : (1 / 5) * d ≤ q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr leakage_low) hd]
  have hqhi : q ≤ (3 / 10) * d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr leakage_high) hd]
  constructor <;> linarith

theorem original_static_action_sufficient (w d q leakage correction rho : ℝ)
    (leakage_low : 1 / 5 ≤ leakage) (leakage_high : leakage ≤ 3 / 10)
    (shared_leakage : q = leakage * d)
    (baseline_low : 9 / 10 ≤ w + d) (baseline_high : w + d ≤ 11 / 10)
    (separating_low : 3 / 5 ≤ w + q) (separating_high : w + q ≤ 13 / 20)
    (correction_low : -(143 / 280) ≤ correction)
    (correction_high : correction ≤ -(37 / 80))
    (rho_low : 0 ≤ rho) (rho_high : rho ≤ 1) :
    |w + correction| ≤ 1 / 8 ∧ |w + correction + rho * d| ≤ 3 / 4 := by
  obtain ⟨hwlo, hwhi⟩ := original_wheel_range w d q leakage leakage_low leakage_high
    shared_leakage baseline_low baseline_high separating_low separating_high
  have hwc : -(1 / 8) ≤ w + correction ∧ w + correction ≤ 1 / 8 := by
    constructor <;> linarith
  have hbase : -(3 / 4) ≤ w + d + correction ∧ w + d + correction ≤ 3 / 4 := by
    constructor <;> linarith
  constructor
  · exact abs_le.mpr hwc
  · apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg rho_low (show 0 ≤ w + d + correction + 3 / 4 by linarith),
        mul_nonneg (show 0 ≤ 1 - rho by linarith)
          (show 0 ≤ w + correction + 3 / 4 by linarith)]
    · nlinarith [mul_nonneg rho_low (show 0 ≤ 3 / 4 - (w + d + correction) by linarith),
        mul_nonneg (show 0 ≤ 1 - rho by linarith)
          (show 0 ≤ 3 / 4 - (w + correction) by linarith)]

theorem endpoint_worlds_satisfy_original_contract :
    (-2 : ℝ) ≤ 27 / 70 ∧ (27 / 70 : ℝ) ≤ 2 ∧
    (-2 : ℝ) ≤ 5 / 7 ∧ (5 / 7 : ℝ) ≤ 2 ∧
    (1 / 5 : ℝ) ≤ 3 / 10 ∧
    (3 / 14 : ℝ) = (3 / 10) * (5 / 7) ∧
    (9 / 10 : ℝ) ≤ 27 / 70 + 5 / 7 ∧ (27 / 70 : ℝ) + 5 / 7 ≤ 11 / 10 ∧
    (3 / 5 : ℝ) ≤ 27 / 70 + 3 / 14 ∧ (27 / 70 : ℝ) + 3 / 14 ≤ 13 / 20 ∧
    (-2 : ℝ) ≤ 47 / 80 ∧ (47 / 80 : ℝ) ≤ 2 ∧
    (-2 : ℝ) ≤ 5 / 16 ∧ (5 / 16 : ℝ) ≤ 2 ∧
    (1 / 16 : ℝ) = (1 / 5) * (5 / 16) ∧
    (9 / 10 : ℝ) ≤ 47 / 80 + 5 / 16 ∧ (47 / 80 : ℝ) + 5 / 16 ≤ 11 / 10 ∧
    (3 / 5 : ℝ) ≤ 47 / 80 + 1 / 16 ∧ (47 / 80 : ℝ) + 1 / 16 ≤ 13 / 20 := by
  norm_num

theorem endpoint_safety_necessary (correction : ℝ)
    (lower_world : |27 / 70 + correction| ≤ 1 / 8)
    (upper_world : |47 / 80 + correction| ≤ 1 / 8) :
    -(143 / 280) ≤ correction ∧ correction ≤ -(37 / 80) := by
  obtain ⟨hl, _⟩ := abs_le.mp lower_world
  obtain ⟨_, hu⟩ := abs_le.mp upper_world
  constructor <;> linarith

#print axioms original_wheel_range
#print axioms original_static_action_sufficient
#print axioms endpoint_worlds_satisfy_original_contract
#print axioms endpoint_safety_necessary
end S12OriginalAction
