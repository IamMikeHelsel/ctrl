import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- AI-written S12 diagnostic. The original priors, baseline and leakage model
are retained, but the hypothetical separating/heldout readings are 2/5 and3/10.
This is NOT a failure of the original observations centered at5/8 and9/16.
Two worlds are individually controllable yet observationally indistinguishable
at the declared heldout precision, even with a perfect separating readout. -/
set_option autoImplicit false
namespace S12Confusability

theorem two_worlds_same_observations :
    (-2 : ℝ) ≤ 6/25 ∧ (6/25 : ℝ) ≤ 2 ∧
    (-2 : ℝ) ≤ 4/25 ∧ (4/25 : ℝ) ≤ 2 ∧
    (-2 : ℝ) ≤ 4/5 ∧ (4/5 : ℝ) ≤ 2 ∧
    (4/25 : ℝ) = (1/5)*(4/5) ∧ (6/25 : ℝ) = (3/10)*(4/5) ∧
    (9/10 : ℝ) ≤ 6/25+4/5 ∧ (6/25 : ℝ)+4/5 ≤ 11/10 ∧
    (9/10 : ℝ) ≤ 4/25+4/5 ∧ (4/25 : ℝ)+4/5 ≤ 11/10 ∧
    (6/25 : ℝ)+4/25 = 3/5 ∧ (4/25 : ℝ)+6/25 = 2/5 ∧
    |(6/25 : ℝ)+(4/25)/2-3/10| ≤ 1/40 ∧
    |(4/25 : ℝ)+(6/25)/2-3/10| ≤ 1/40 := by norm_num

theorem each_world_has_a_uniform_safe_action (rho : ℝ)
    (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) :
    |(6/25 : ℝ)-1/3| ≤ 1/8 ∧
    |(6/25 : ℝ)-1/3+rho*(4/5)| ≤ 3/4 ∧
    |(4/25 : ℝ)-1/4| ≤ 1/8 ∧
    |(4/25 : ℝ)-1/4+rho*(4/5)| ≤ 3/4 := by
  refine ⟨by norm_num, ?_, by norm_num, ?_⟩
  all_goals apply abs_le.mpr; constructor <;> linarith

theorem no_common_safe_action (correction : ℝ)
    (worldA_endpoint : |(6/25 : ℝ)+correction+4/5| ≤ 3/4)
    (worldB_wheel : |(4/25 : ℝ)+correction| ≤ 1/8) : False := by
  obtain ⟨_, ha⟩ := abs_le.mp worldA_endpoint
  obtain ⟨hb, _⟩ := abs_le.mp worldB_wheel
  linarith

theorem heldout_pair_separation_threshold (eps : ℝ) (h : eps < 1/50) :
    ¬ ∃ observation : ℝ,
      |(6/25 : ℝ)+(4/25)/2-observation| ≤ eps ∧
      |(4/25 : ℝ)+(6/25)/2-observation| ≤ eps := by
  rintro ⟨observation, ha, hb⟩
  obtain ⟨_, haU⟩ := abs_le.mp ha
  obtain ⟨hbL, _⟩ := abs_le.mp hb
  linarith

#print axioms two_worlds_same_observations
#print axioms each_world_has_a_uniform_safe_action
#print axioms no_common_safe_action
#print axioms heldout_pair_separation_threshold
end S12Confusability
