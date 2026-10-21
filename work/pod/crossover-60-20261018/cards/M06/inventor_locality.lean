import Mathlib

namespace M06Inventor

-- Arithmetic consequence of the graph-boundary identity. The graph-to-count
-- binding is a separate hand proof, not hidden in this scalar lemma.
theorem small_subset_cannot_improve
    (k a b internal crossed : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hi : 0 ≤ internal)
    (hsize : a + b ≤ 2*k) (hcross : crossed ≤ a*b) :
    0 ≤ k*(a+b) + 2*internal - 2*crossed := by
  have hp : 0 ≤ (a+b)*(2*k-a-b) := mul_nonneg (add_nonneg ha hb) (by linarith)
  nlinarith [sq_nonneg (a-b)]

theorem first_larger_subset_improves (k : ℝ) :
    k*(k+(k+1))-2*k*(k+1) = -k := by ring

theorem bad_cut_exceeds_target (k : ℝ) (hk : 0 < k) :
    2*(8*k)^2/47 < 4*k^2 := by
  have hsq : 0 < k^2 := sq_pos_of_pos hk
  nlinarith

theorem middle_density : (8:ℚ)/47 < 3/8 ∧ (3:ℚ)/8 < 49/125 := by
  norm_num

#print axioms small_subset_cannot_improve
#print axioms first_larger_subset_improves
#print axioms bad_cut_exceeds_target
#print axioms middle_density
end M06Inventor
