import Mathlib
namespace FactoryStatementCheck
def statement : Prop :=
  ∀ (v c rate : ℝ → ℝ) (a acc V A S R t : ℝ),
    HasDerivAt v a (c t) → HasDerivAt c (rate t) t → HasDerivAt rate acc t →
    |v (c t)| ≤ V → |a| ≤ A → |rate t| ≤ S → |acc| ≤ R →
    0 ≤ V → 0 ≤ A → 0 ≤ S → 0 ≤ R →
    HasDerivAt (fun x => v (c x) * rate x)
      (a * (rate t)^2 + v (c t) * acc) t ∧
    |a * (rate t)^2 + v (c t) * acc| ≤ A * S^2 + V * R
#check statement
end FactoryStatementCheck
