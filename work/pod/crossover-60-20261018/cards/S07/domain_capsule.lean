import Mathlib.Tactic
namespace S07Capsule

theorem original_core_margin (x : ℝ)
    (hx : x^2 ≤ (3550075/11131832:ℝ)*12) : |x| ≤ 49/25 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x-49/25), sq_nonneg (x+49/25)]

theorem capsule_travel (x d : ℝ) (hx : |x| ≤ 49/25) (hd : |d| ≤ 1/25) :
    |x+d| ≤ 2 := by
  have h := abs_add_le x d
  linarith

theorem strict_superset_witness :
    (189/50:ℝ)*(89/50)^2 < 12 ∧ 12 < (189/50:ℝ)*(91/50)^2 ∧
    (91/50:ℝ)=(89/50)+(1/25) := by norm_num

theorem smaller_capsule_volume_arithmetic :
    (3317/1000:ℝ)^2>11 ∧ (1945/1000:ℝ)^2>189/50 ∧
    (3464/1000:ℝ)^2<12 ∧
    (44*(3317/1000:ℝ)+(33/4)*(1945/1000))/(48*(3464/1000))<1 := by norm_num

#print axioms original_core_margin
#print axioms capsule_travel
#print axioms strict_superset_witness
#print axioms smaller_capsule_volume_arithmetic
end S07Capsule
