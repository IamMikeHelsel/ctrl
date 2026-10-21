import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
set_option autoImplicit false
namespace R10RetainedFIR
/-- On the retained ordinary-return piece t=.72+u, the quadratic acceleration
has its exact minimum at u=.05. Coefficients are reconstructed from both signed events. -/
theorem ordinary_acceleration_vertex (u : ℝ) :
    (-9/16:ℝ)-(15/4)*u+(75/2)*u^2 = (75/2)*(u-1/20)^2-21/32 := by ring

theorem ordinary_acceleration_lower (u : ℝ) :
    (-21/32:ℝ) ≤ (-9/16:ℝ)-(15/4)*u+(75/2)*u^2 := by
  rw [ordinary_acceleration_vertex]
  nlinarith [sq_nonneg (u-1/20)]

theorem ordinary_acceleration_violation :
    |(-9/16:ℝ)-(15/4)*(1/20)+(75/2)*(1/20)^2|=21/32 ∧
    (1/2:ℝ)<21/32 ∧ (18/25:ℝ)+1/20=77/100 := by norm_num

theorem far_acceleration_vertex (u : ℝ) :
    (-13/16:ℝ)-(25/4)*u+(225/4)*u^2 = (225/4)*(u-1/18)^2-71/72 := by ring

theorem far_rejection_witness :
    |(-13/16:ℝ)-(25/4)*(1/18)+(225/4)*(1/18)^2|=71/72 ∧
    (1/2:ℝ)<71/72 ∧ (18/25:ℝ)+1/18=349/450 ∧ (15/2:ℝ)<45/4 := by norm_num

/-- The ordinary return passes the jerk-only criterion despite its acceleration failure. -/
theorem jerk_gate_is_insufficient :
    (25/4:ℝ) ≤ 15/2 ∧ ¬ (21/32:ℝ) ≤ 1/2 := by norm_num

/-- Late-buffered quadratic piece includes its exact acceleration boundary. -/
theorem buffered_piece_acceleration (u : ℝ) (hu : 0≤u) (hu1 : u≤1/5) :
    |(-1/2:ℝ)+(25/2)*u^2| ≤ 1/2 := by
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg u]
  · nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]

/-- Four nonnegative weights summing to one preserve an absolute bound. -/
theorem convex_four_bound (w0 w1 w2 w3 b0 b1 b2 b3 L : ℝ)
    (hw0 : 0≤w0) (hw1 : 0≤w1) (hw2 : 0≤w2) (hw3 : 0≤w3)
    (hw : w0+w1+w2+w3=1)
    (hb0 : |b0|≤L) (hb1 : |b1|≤L) (hb2 : |b2|≤L) (hb3 : |b3|≤L) :
    |w0*b0+w1*b1+w2*b2+w3*b3|≤L := by
  rcases abs_le.mp hb0 with ⟨hl0,hu0⟩
  rcases abs_le.mp hb1 with ⟨hl1,hu1⟩
  rcases abs_le.mp hb2 with ⟨hl2,hu2⟩
  rcases abs_le.mp hb3 with ⟨hl3,hu3⟩
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hw0 (show 0≤b0+L by linarith),
      mul_nonneg hw1 (show 0≤b1+L by linarith),
      mul_nonneg hw2 (show 0≤b2+L by linarith),
      mul_nonneg hw3 (show 0≤b3+L by linarith)]
  · nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hu0),
      mul_nonneg hw1 (sub_nonneg.mpr hu1),
      mul_nonneg hw2 (sub_nonneg.mpr hu2),
      mul_nonneg hw3 (sub_nonneg.mpr hu3)]

/-- Reusable exact all-time bound for cubic reference-velocity pieces. -/
theorem bernstein_cubic_bound (u b0 b1 b2 b3 L : ℝ) (hu : 0≤u) (hu1 : u≤1)
    (hb0 : |b0|≤L) (hb1 : |b1|≤L) (hb2 : |b2|≤L) (hb3 : |b3|≤L) :
    |(1-u)^3*b0 + (3*u*(1-u)^2)*b1 + (3*u^2*(1-u))*b2 + u^3*b3|≤L := by
  have hv : 0≤1-u := by linarith
  apply convex_four_bound _ _ _ _ _ _ _ _ L
  · positivity
  · positivity
  · positivity
  · positivity
  · ring
  · exact hb0
  · exact hb1
  · exact hb2
  · exact hb3

/-- A service deadline preceding execution is a failed causal promise; no plant claim. -/
theorem predelivery_service_failure : (51/100:ℝ)<13/25 := by norm_num

#print axioms ordinary_acceleration_vertex
#print axioms ordinary_acceleration_lower
#print axioms ordinary_acceleration_violation
#print axioms far_acceleration_vertex
#print axioms far_rejection_witness
#print axioms jerk_gate_is_insufficient
#print axioms buffered_piece_acceleration
#print axioms convex_four_bound
#print axioms bernstein_cubic_bound
#print axioms predelivery_service_failure
end R10RetainedFIR
