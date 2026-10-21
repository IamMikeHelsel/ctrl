import Mathlib.Data.Real.Basic
import Mathlib.Tactic
namespace CampaignV10Wide

theorem wide_frobenius_budget (a b c : ℝ)
    (ha : |a| ≤ 1/100) (hb : |b| ≤ 1/100) (hc : |c| ≤ 1/100) :
    8*(a^2+b^2+c^2)/(1+a^2+b^2+c^2) ≤ (1/20 : ℝ)^2 := by
  have ha2 : a^2 ≤ (1/100 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) (by norm_num)).2 ha
  have hb2 : b^2 ≤ (1/100 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) (by norm_num)).2 hb
  have hc2 : c^2 ≤ (1/100 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg c) (by norm_num)).2 hc
  apply (div_le_iff₀ (by positivity : 0 < 1+a^2+b^2+c^2)).2
  nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg c]

theorem wide_constants :
    (24/10003 : ℝ) < (1/20)^2 ∧
    ((1/10 : ℝ)+(3/2)*(2/25))/(1-2/25) = 11/46 ∧
    (11/46 : ℝ) < 1/4 := by norm_num

/-- Sharp cutoff for THIS conservative algebraic bound, not actual feasibility. -/
theorem outer_bound_cutoff (delta : ℝ) (hden : 0 < 1-delta*(8/5)) :
    ((1/10 : ℝ)+(3/2)*(delta*(8/5)))/(1-delta*(8/5)) < 1/4 ↔
    delta < 3/56 := by
  rw [div_lt_iff₀ hden]
  constructor <;> intro h <;> nlinarith
end CampaignV10Wide
#print axioms CampaignV10Wide.wide_frobenius_budget
#print axioms CampaignV10Wide.wide_constants
#print axioms CampaignV10Wide.outer_bound_cutoff
