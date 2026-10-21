import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- AI-written negative control, explicitly changing the source model prior:
   add 1/2 <= |d| <= 1. It is not a counterexample to the original checker.
   Baseline stage only: original separating row is NOT used.
   Heldout row is unchanged, but its interval is changed to [19/20,21/20].
   Original baseline, redundant trial and common-leakage interpretation remain. -/
namespace S12Gap

theorem positive_branch_upper (w d q : ℚ)
    (baseline : w + d ≤ 11 / 10)
    (leakage : q ≤ (3 / 10) * d) (amplitude : 1 / 2 ≤ d) :
    w + q / 2 ≤ 27 / 40 := by
  linarith

theorem negative_branch_lower (w d q : ℚ)
    (baseline : 9 / 10 ≤ w + d)
    (leakage : (3 / 10) * d ≤ q) (amplitude : d ≤ -(1 / 2)) :
    53 / 40 ≤ w + q / 2 := by
  linarith

theorem heldout_rejected (w d q : ℚ)
    (baseline_low : 9 / 10 ≤ w + d) (baseline_high : w + d ≤ 11 / 10)
    (branches : (1 / 2 ≤ d ∧ q ≤ (3 / 10) * d) ∨
      (d ≤ -(1 / 2) ∧ (3 / 10) * d ≤ q))
    (heldout_low : 19 / 20 ≤ w + q / 2)
    (heldout_high : w + q / 2 ≤ 21 / 20) : False := by
  rcases branches with ⟨hd, hq⟩ | ⟨hd, hq⟩
  · have hp := positive_branch_upper w d q baseline_high hq hd
    linarith
  · have hn := negative_branch_lower w d q baseline_low hq hd
    linarith

theorem two_feasible_prediction_values_straddle_observation :
    (3 / 5 : ℚ) + 1 / 2 = 11 / 10 ∧
    (3 / 20 : ℚ) = (3 / 10) * (1 / 2) ∧
    (3 / 5 : ℚ) + (3 / 20) / 2 = 27 / 40 ∧
    (7 / 5 : ℚ) - 1 / 2 = 9 / 10 ∧
    (-3 / 20 : ℚ) = (3 / 10) * (-(1 / 2)) ∧
    (7 / 5 : ℚ) + (-3 / 20) / 2 = 53 / 40 ∧
    (27 / 40 : ℚ) < 19 / 20 ∧ (21 / 20 : ℚ) < 53 / 40 ∧
    ((27 / 40 : ℚ) + 53 / 40) / 2 = 1 := by
  norm_num

#print axioms positive_branch_upper
#print axioms negative_branch_lower
#print axioms heldout_rejected
#print axioms two_feasible_prediction_values_straddle_observation
end S12Gap
