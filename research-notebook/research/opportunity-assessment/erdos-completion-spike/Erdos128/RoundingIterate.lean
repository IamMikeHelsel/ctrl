import Erdos128.Rounding

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# Iterating pair rounding

This file iterates `exists_pair_rounding`.  Strong induction on the number of
non-integral coordinates produces a bounded profile with the same total mass,
no larger edge cost, and at most one coordinate outside `{0, 1}`.
-/

namespace Erdos128

open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The vertices at which a rational profile is neither zero nor one. -/
def nonIntegralCoords (x : V → ℚ) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun v ↦ ¬ IsZeroOrOne (x v)

omit [DecidableEq V] in
@[simp] lemma mem_nonIntegralCoords {x : V → ℚ} {v : V} :
    v ∈ nonIntegralCoords x ↔ ¬ IsZeroOrOne (x v) := by
  simp [nonIntegralCoords]

omit [Fintype V] [DecidableEq V] in
/-- Under `[0,1]` bounds, a non-integral coordinate is strictly fractional. -/
lemma strict_fractional_of_not_zero_or_one {x : V → ℚ} {v : V}
    (hx : 0 ≤ x v ∧ x v ≤ 1) (hv : ¬ IsZeroOrOne (x v)) :
    0 < x v ∧ x v < 1 := by
  constructor
  · rcases hx.1.lt_or_eq with hpos | hzero
    · exact hpos
    · exact False.elim (hv (Or.inl hzero.symm))
  · rcases hx.2.lt_or_eq with hlt | hone
    · exact hlt
    · exact False.elim (hv (Or.inr hone))

/-- Iterated pair rounding leaves at most one non-integral coordinate. -/
theorem exists_rounding_at_most_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℚ) (hx : ∀ w, 0 ≤ x w ∧ x w ≤ 1) :
    ∃ y : V → ℚ,
      (∀ w, 0 ≤ y w ∧ y w ≤ 1) ∧
      (∑ w, y w) = ∑ w, x w ∧
      edgeCost G y ≤ edgeCost G x ∧
      (nonIntegralCoords y).card ≤ 1 := by
  classical
  induction hcard : (nonIntegralCoords x).card using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hn : n ≤ 1
      · exact ⟨x, hx, rfl, le_rfl, hcard ▸ hn⟩
      · have hn' : 1 < (nonIntegralCoords x).card := by omega
        obtain ⟨u, hu, v, hv, huv⟩ :=
          Finset.one_lt_card.mp hn'
        have hu' : ¬ IsZeroOrOne (x u) := mem_nonIntegralCoords.mp hu
        have hv' : ¬ IsZeroOrOne (x v) := mem_nonIntegralCoords.mp hv
        have hxu := strict_fractional_of_not_zero_or_one (hx u) hu'
        have hxv := strict_fractional_of_not_zero_or_one (hx v) hv'
        obtain ⟨y, hybounds, hysum, hycost, hyintegral, hyother⟩ :=
          exists_pair_rounding G x huv hx hxu hxv
        have hsubset : nonIntegralCoords y ⊆ nonIntegralCoords x := by
          intro w hwy
          by_cases hwu : w = u
          · simpa [hwu] using hu
          · by_cases hwv : w = v
            · simpa [hwv] using hv
            · have hyx : y w = x w := hyother w hwu hwv
              exact mem_nonIntegralCoords.mpr <| by
                simpa [hyx] using mem_nonIntegralCoords.mp hwy
        have hmissing : ∃ w ∈ nonIntegralCoords x, w ∉ nonIntegralCoords y := by
          rcases hyintegral with hyu | hyv
          · exact ⟨u, hu, by simp [mem_nonIntegralCoords, hyu]⟩
          · exact ⟨v, hv, by simp [mem_nonIntegralCoords, hyv]⟩
        have hstrict : nonIntegralCoords y ⊂ nonIntegralCoords x :=
          (Finset.ssubset_iff_of_subset hsubset).2 hmissing
        have hdecrease : (nonIntegralCoords y).card < n := by
          rw [← hcard]
          exact Finset.card_lt_card hstrict
        obtain ⟨z, hzbounds, hzsum, hzcost, hzcard⟩ :=
          ih (nonIntegralCoords y).card hdecrease y hybounds rfl
        exact ⟨z, hzbounds, hzsum.trans hysum,
          hzcost.trans hycost, hzcard⟩

end

end Erdos128
