import Mathlib
namespace FactoryStatementCheck
def statement : Prop :=
  ∀ {α : Type} [DecidableEq α] (U : Finset α) (k : ℕ)
    (C : Fin k → Finset α) (cap : Fin k → ℕ),
    (∀ i, (U ∩ C i).card ≤ cap i) →
    (∑ i, cap i) < U.card →
    ¬ (∀ x ∈ U, ∃ i, x ∈ C i)
#check statement
end FactoryStatementCheck
