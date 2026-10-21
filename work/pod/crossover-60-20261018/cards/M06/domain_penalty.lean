import Mathlib.Data.Finset.Sum
import Mathlib.Tactic
namespace M06Penalty

def bit (b : Bool) : ℤ := if b then 1 else 0
def crossing (a b : Bool) : ℤ := if a == b then 0 else 1

theorem edge_penalty (sa sb ta tb : Bool)
    (ha : ¬(sa = true ∧ ta = true)) (hb : ¬(sb = true ∧ tb = true)) :
    crossing (sa || ta) (sb || tb) - crossing sa sb =
      bit ta * (1 - 2 * bit sb) + bit tb * (1 - 2 * bit sa) -
      2 * bit ta * bit tb := by
  cases sa <;> cases sb <;> cases ta <;> cases tb <;>
    simp_all [crossing, bit]

/-- Exact arbitrary extension; unlike the independent case, internal T edges are penalized. -/
theorem arbitrary_extension_exact {V : Type*} (E : Finset (V × V))
    (S T : V → Bool) (hdis : ∀ v, ¬(S v = true ∧ T v = true)) :
    (∑ e ∈ E, crossing (S e.1 || T e.1) (S e.2 || T e.2)) -
      (∑ e ∈ E, crossing (S e.1) (S e.2)) =
    ∑ e ∈ E, (bit (T e.1) * (1 - 2 * bit (S e.2)) +
      bit (T e.2) * (1 - 2 * bit (S e.1)) - 2 * bit (T e.1) * bit (T e.2)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  exact edge_penalty _ _ _ _ (hdis _) (hdis _)

#print axioms edge_penalty
#print axioms arbitrary_extension_exact
end M06Penalty
