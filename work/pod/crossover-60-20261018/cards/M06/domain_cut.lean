import Mathlib.Data.Finset.Sum
import Mathlib.Tactic

namespace M06Domain

def bit (b : Bool) : ℤ := if b then 1 else 0
def crossing (a b : Bool) : ℤ := if a == b then 0 else 1

/-- An independent set outside a cut side has additive flip gains. -/
theorem edge_flip (sa sb ta tb : Bool)
    (ha : ¬(sa = true ∧ ta = true)) (hb : ¬(sb = true ∧ tb = true))
    (hi : ¬(ta = true ∧ tb = true)) :
    crossing (sa || ta) (sb || tb) - crossing sa sb =
      bit ta * (1 - 2 * bit sb) + bit tb * (1 - 2 * bit sa) := by
  cases sa <;> cases sb <;> cases ta <;> cases tb <;>
    simp_all [crossing, bit]

/-- E contains actual edges, once each. S and T are vertex predicates; no balance constraint. -/
theorem independent_flip_exact {V : Type*} (E : Finset (V × V))
    (S T : V → Bool)
    (hdis : ∀ v, ¬(S v = true ∧ T v = true))
    (hind : ∀ e ∈ E, ¬(T e.1 = true ∧ T e.2 = true)) :
    (∑ e ∈ E, crossing (S e.1 || T e.1) (S e.2 || T e.2)) -
      (∑ e ∈ E, crossing (S e.1) (S e.2)) =
    ∑ e ∈ E, (bit (T e.1) * (1 - 2 * bit (S e.2)) +
      bit (T e.2) * (1 - 2 * bit (S e.1))) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  exact edge_flip _ _ _ _ (hdis _) (hdis _) (hind e he)

/-- Assumed normalized degree variance and neighbor-cut lower bound give this gate. -/
theorem variance_gate (r variance cross internal : ℝ)
    (hcut : internal = r / 2 - cross)
    (hneigh : r ^ 2 + variance ≤ cross)
    (hvar : r / 2 - r ^ 2 - 2 / 47 ≤ variance) :
    internal ≤ 2 / 47 := by linarith

theorem maximum_variance_requirement (r : ℝ) :
    r / 2 - r ^ 2 - 2 / 47 ≤ 15 / 752 := by
  nlinarith [sq_nonneg (r - 1 / 4)]

theorem clebsch_route_gap : (11 : ℚ) / 256 - 2 / 47 = 5 / 12032 := by norm_num

#print axioms edge_flip
#print axioms independent_flip_exact
#print axioms variance_gate
#print axioms maximum_variance_requirement
#print axioms clebsch_route_gap
end M06Domain
