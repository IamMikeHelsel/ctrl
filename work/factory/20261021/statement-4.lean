import Mathlib
namespace FactoryStatementCheck
def statement : Prop :=
  ∀ (q v a δ T : ℝ) (r : ℝ → ℝ),
    (∀ t ∈ Set.Icc (0 : ℝ) T, |r t| ≤ δ / 2 * t^2) →
    (∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ q + v*t + (a-δ)/2*t^2) →
    ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ q + v*t + a/2*t^2 + r t
#check statement
end FactoryStatementCheck
