import Mathlib
namespace FactoryStatementCheck
def statement : Prop :=
  ∀ (x : ℕ → ℝ) (ρ ε L : ℝ), 0 ≤ ρ →
    ε ≤ (1 - ρ) * L →
    (∀ n, x (n + 1) ≤ ρ * x n + ε) →
    ∀ n, x n ≤ ρ^n * (x 0 - L) + L
#check statement
end FactoryStatementCheck
