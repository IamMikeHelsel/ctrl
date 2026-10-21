import Mathlib.Tactic
namespace S07Budget

theorem exact_floor (R : ℝ) :
    (13:ℝ)*(1/5+(5/451)⁻¹)*(1/100)^2 ≤ (5/451)*R ↔
    662519/62500 ≤ R := by norm_num; constructor <;> intro h <;> linarith

/-- The unchanged budget admits a point with actual request -3/2, not just an abstract sector. -/
theorem budget_contains_active_witness (R : ℝ)
    (h : (13:ℝ)*(1/5+(5/451)⁻¹)*(1/100)^2 ≤ (5/451)*R) :
    (278/25:ℝ)*(3/4)^2 < R ∧ (-2*(3/4:ℝ)) < -1 := by
  have hf := (exact_floor R).mp h
  constructor <;> norm_num at * <;> linarith

theorem nonempty_radius_interval :
    (662519/62500:ℝ) < 12 ∧ (12:ℝ) < 44527328/3550075 := by norm_num

#print axioms exact_floor
#print axioms budget_contains_active_witness
#print axioms nonempty_radius_interval
end S07Budget
