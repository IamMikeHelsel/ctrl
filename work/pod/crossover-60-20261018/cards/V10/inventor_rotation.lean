import Mathlib.Tactic

/- Scalar consequences of the exact camera fixture. No solver or added axioms.
   The general matrix-to-scalar binding is documented in inventor.md. -/
namespace CrossoverV10Inventor

theorem column_bound (x y z gamma : ℝ)
    (hunit : x^2 + y^2 + z^2 = 1)
    (hcone : x^2 + y^2 ≤ gamma^2 * z^2) :
    1 ≤ (1+gamma^2)*z^2 := by
  nlinarith

theorem rotation_lower_bound (gamma z1 z3 : ℝ)
    (hg : 0 ≤ gamma)
    (h1 : 1 ≤ (1+gamma^2)*z1^2)
    (h3 : 1 ≤ (1+gamma^2)*z3^2)
    (hrow : z1^2+z3^2 ≤ 1) : 1 ≤ gamma := by
  have hfactor : 0 ≤ 1+gamma^2 := by positivity
  have hmul := mul_nonneg hfactor (show 0 ≤ 1-z1^2-z3^2 by linarith)
  have hsquare : 1 ≤ gamma^2 := by nlinarith
  by_contra h
  have hlt : gamma < 1 := lt_of_not_ge h
  have hproduct : 0 ≤ gamma*(1-gamma) := mul_nonneg hg (by linarith)
  nlinarith

theorem half_threshold_impossible (z1 z3 : ℝ)
    (h1 : 1 ≤ (1+(1/2:ℝ)^2)*z1^2)
    (h3 : 1 ≤ (1+(1/2:ℝ)^2)*z3^2)
    (hrow : z1^2+z3^2 ≤ 1) : False := by
  have h := rotation_lower_bound (1/2) z1 z3 (by norm_num) h1 h3 hrow
  norm_num at h

theorem algebraic_attainer :
    let q := Real.sqrt (2:ℝ)/2
    0 < q ∧ q^2+q^2=1 ∧ q*q+(-q)*q=0 ∧ q/q=1 ∧ (-q)/q = -1 := by
  dsimp
  have hs : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hq : Real.sqrt (2:ℝ)/2 ≠ 0 := ne_of_gt (by positivity)
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · ring
  · exact div_self hq
  · rw [neg_div, div_self hq]

theorem rational_convex_mean_depths :
    (0:ℝ)<4/5 ∧ (0:ℝ)<3/5 ∧
    ((3/5:ℝ)+(-3/5))/2=0 ∧ ((-4/5:ℝ)+(4/5))/2=0 ∧
    ((4/5:ℝ)+(4/5))/2=4/5 ∧ ((3/5:ℝ)+(3/5))/2=3/5 := by
  norm_num

#print axioms column_bound
#print axioms rotation_lower_bound
#print axioms half_threshold_impossible
#print axioms algebraic_attainer
#print axioms rational_convex_mean_depths
end CrossoverV10Inventor
