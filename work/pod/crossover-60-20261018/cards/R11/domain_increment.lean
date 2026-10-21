import Mathlib.Data.Real.Basic
import Mathlib.Tactic
namespace CampaignR11
/-- Exact coefficient from P11+2*norm(C)^2 for root's ramp matrix. -/
theorem increment_young_coefficient :
    (1785/158:ℝ)+2*((1515/158)^2+(-165/79)^2+(-357/316)^2) = 10308009/49928 ∧
    (10308009/49928:ℝ) < 207 := by norm_num

theorem increment_energy_budget :
    (39/40:ℝ)*(1/2000000)+207*(1/200000)^2 < 1/2000000 := by norm_num

/-- Conditional scalar energy admission; deriving this recurrence from P and
    bounding actual sensor/inner-error increments remain separate obligations. -/
theorem increment_energy_step (energy next u : ℝ)
    (he : energy ≤ 1/2000000) (hu : |u| ≤ 1/200000)
    (hstep : next ≤ (39/40)*energy+207*u^2) : next ≤ 1/2000000 := by
  obtain ⟨hl,hh⟩ := abs_le.mp hu
  have hp : 0 ≤ ((1/200000:ℝ)-u)*((1/200000:ℝ)+u) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith
end CampaignR11
#print axioms CampaignR11.increment_young_coefficient
#print axioms CampaignR11.increment_energy_budget
#print axioms CampaignR11.increment_energy_step
