import Mathlib.Tactic
namespace S07Membership
-- Scalar quadratic certificate: positive curvature and boundary KKT signs suffice.
theorem difference (A B C d t : ℝ) :
 (C-2*B*t+A*t^2)-(C-2*B*d+A*d^2)=A*(t-d)^2+2*(A*d-B)*(t-d) := by ring

theorem optimal (A B C d t : ℝ) (hA : 0≤A) (hK : 0≤(A*d-B)*(t-d)) :
 C-2*B*d+A*d^2≤C-2*B*t+A*t^2 := by
 have he := difference A B C d t
 have hq := mul_nonneg hA (sq_nonneg (t-d))
 nlinarith

theorem box_boundary (A B d t D : ℝ) (ht0 : -D≤t) (ht1 : t≤D)
 (h : (d = -D ∧ 0≤A*d-B) ∨ (d = D ∧ A*d-B≤0) ∨ A*d-B=0) :
 0≤(A*d-B)*(t-d) := by
 rcases h with ⟨rfl,hh⟩ | ⟨rfl,hh⟩ | hh
 · exact mul_nonneg hh (by linarith)
 · exact mul_nonneg_of_nonpos_of_nonpos hh (by linarith)
 · rw [hh]; simp
end S07Membership
#print axioms S07Membership.difference
#print axioms S07Membership.optimal
#print axioms S07Membership.box_boundary
