import Mathlib.Data.Real.Basic
import Mathlib.Tactic
namespace CampaignS04Action
/-- Frozen static -1/2 action with original lambda and rho. Extra prior and
redundant trial constraints may be retained; no software or physics bridge. -/
theorem original_acceptance (w d lam rho : ℝ)
    (hlamlo : (1 / 5 : ℝ) ≤ lam) (hlamhi : lam ≤ (3 / 10 : ℝ))
    (hblo : (9 / 10 : ℝ) ≤ w + d) (hbhi : w + d ≤ (11 / 10 : ℝ))
    (hslo : (3 / 5 : ℝ) ≤ w + lam * d) (hshi : w + lam * d ≤ (13 / 20 : ℝ))
    (hrlo : 0 ≤ rho) (hrhi : rho ≤ 1) :
    |w - 1 / 2| ≤ (1 / 8 : ℝ) ∧ |w - 1 / 2 + rho * d| ≤ (3 / 4 : ℝ) := by
  have hd : 0 ≤ d := by
    by_contra h
    have hdn : d ≤ 0 := le_of_lt (lt_of_not_ge h)
    have hp : 0 ≤ (lam - 1) * d :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hdn
    nlinarith
  have hpl : 0 ≤ (lam - 1 / 5) * d := mul_nonneg (by linarith) hd
  have hpu : 0 ≤ (3 / 10 - lam) * d := mul_nonneg (by linarith) hd
  have hwlo : (27 / 70 : ℝ) ≤ w := by nlinarith
  have hwhi : w ≤ (47 / 80 : ℝ) := by nlinarith
  have hrp : 0 ≤ rho * d := mul_nonneg hrlo hd
  have hru : 0 ≤ (1 - rho) * d := mul_nonneg (by linarith) hd
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem rejected_action_witness :
    (1 / 5 : ℝ) ≤ 1 / 4 ∧ (1 / 4 : ℝ) ≤ 3 / 10 ∧
    (9 / 10 : ℝ) ≤ 1 / 2 + 1 / 2 ∧ (1 / 2 : ℝ) + 1 / 2 ≤ 11 / 10 ∧
    (3 / 5 : ℝ) ≤ 1 / 2 + (1 / 4) * (1 / 2) ∧
    (1 / 2 : ℝ) + (1 / 4) * (1 / 2) ≤ 13 / 20 ∧
    (1 / 8 : ℝ) < |(1 / 2 : ℝ) - 1| := by norm_num
end CampaignS04Action
#print axioms CampaignS04Action.original_acceptance
#print axioms CampaignS04Action.rejected_action_witness
