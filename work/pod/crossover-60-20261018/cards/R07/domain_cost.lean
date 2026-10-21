import Mathlib.Tactic
namespace R07Cost
/-- Orthogonal decomposition relative to any nominal joint velocity, including
one that does not already realize the demanded task rate. -/
theorem cost_decomposition (v n u₁ u₂ : ℝ) :
    (v/2+n-u₁)^2+(v/2-n-u₂)^2 =
    (v-u₁-u₂)^2/2+2*(n-(u₁-u₂)/2)^2 := by ring

theorem cost_order (v n m u₁ u₂ : ℝ)
    (h : (n-(u₁-u₂)/2)^2≤(m-(u₁-u₂)/2)^2) :
    (v/2+n-u₁)^2+(v/2-n-u₂)^2≤(v/2+m-u₁)^2+(v/2-m-u₂)^2 := by
  rw [cost_decomposition,cost_decomposition]
  linarith

theorem unchanged_iff (v n u₁ u₂ : ℝ) :
    (v/2+n=u₁ ∧ v/2-n=u₂) ↔ (u₁+u₂=v ∧ n=(u₁-u₂)/2) := by
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

#print axioms cost_decomposition
#print axioms cost_order
#print axioms unchanged_iff
end R07Cost
