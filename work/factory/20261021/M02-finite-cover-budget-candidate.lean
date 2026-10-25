import Mathlib
set_option maxHeartbeats 400000
namespace Factory
def statement : Prop :=
  ∀ {α : Type} [DecidableEq α] (U : Finset α) (k : ℕ)
    (C : Fin k → Finset α) (cap : Fin k → ℕ),
    (∀ i, (U ∩ C i).card ≤ cap i) →
    (∑ i, cap i) < U.card →
    ¬ (∀ x ∈ U, ∃ i, x ∈ C i)
theorem solution : statement := by
  unfold statement
  intro α _inst U k C cap hcap hlt hforall
  have hUsub : U ⊆ (Finset.univ.biUnion fun i => U ∩ C i) := by
    intro x hxU
    rcases hforall x hxU with ⟨i, hi⟩
    have : x ∈ U ∩ C i := by
      exact ⟨hxU, hi⟩
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, this⟩
  have hcardUle : U.card ≤ (Finset.univ.biUnion fun i => U ∩ C i).card :=
    Finset.card_le_of_subset hUsub
  have hcard_le_sum : (Finset.univ.biUnion fun i => U ∩ C i).card ≤ ∑ i, cap i := by
    have hle : (Finset.univ.biUnion fun i => U ∩ C i).card ≤
        ∑ i, (U ∩ C i).card := by
      simpa using Finset.card_biUnion_le (s:=Finset.univ) (t:=fun i => U ∩ C i)
    refine le_trans hle ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hcap i
  have : U.card ≤ ∑ i, cap i := le_trans hcardUle hcard_le_sum
  exact not_lt.mpr this hlt
example : statement := solution
#print axioms solution
end Factory
