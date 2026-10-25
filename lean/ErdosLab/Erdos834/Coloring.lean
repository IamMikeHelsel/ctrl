import Challenge.Erdos834

/-!
Reusable coloring lemmas developed with OpenAI Codex, 2026-10-18.
These change no definition in the frozen statement's dependencies.
-/

namespace Research.HypergraphCertificates

open Finset

/-- Recoloring through an injection preserves a proper coloring. -/
theorem recolor {V C D : Type*} [DecidableEq V]
    {H : Finset (Finset V)} {c : V → C} (hc : H.IsProperHypergraphColoring c)
    (f : C → D) (hf : Function.Injective f) :
    H.IsProperHypergraphColoring (fun v ↦ f (c v)) := by
  intro e he
  obtain ⟨x, hx, y, hy, hxy⟩ := hc e he
  exact ⟨x, hx, y, hy, fun h ↦ hxy (hf h)⟩

/-- Every three-vertex edge imposes a not-all-equal constraint. -/
theorem triple_constraint {V C : Type*} [DecidableEq V]
    {H : Finset (Finset V)} {c : V → C} (hc : H.IsProperHypergraphColoring c)
    {a b d : V} (he : {a, b, d} ∈ H) : ¬ (c a = c b ∧ c b = c d) := by
  rintro ⟨hab, hbd⟩
  have same : ∀ x ∈ ({a, b, d} : Finset V), c x = c a := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · rfl
    · exact hab.symm
    · exact (hab.trans hbd).symm
  obtain ⟨x, hx, y, hy, hxy⟩ := hc {a, b, d} he
  exact hxy ((same x hx).trans (same y hy).symm)

/-- Positive degree makes vertex-deletion witnesses redundant: choose an incident edge,
then restrict its deletion coloring to the smaller remaining edge family. -/
theorem vertex_deletion_from_edge_deletion {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) (k : ℕ)
    (edge : ∀ e ∈ H, (H.erase e).HypergraphColorable k)
    (degree : ∀ v, 0 < H.hypergraphDegree v) :
    ∀ v, (H.filter (fun e ↦ v ∉ e)).HypergraphColorable k := by
  intro v
  obtain ⟨e, he⟩ := Finset.card_pos.mp (degree v)
  obtain ⟨heH, hve⟩ := Finset.mem_filter.mp he
  obtain ⟨c, hc⟩ := edge e heH
  refine ⟨c, ?_⟩
  intro f hf
  obtain ⟨hfH, hvf⟩ := Finset.mem_filter.mp hf
  apply hc f
  exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hvf hve, hfH⟩

/-- Boolean cubic monochromatic indicators reduce exactly to a quadratic polynomial. -/
theorem monochromatic_polynomial (a b c : ℝ) :
    a * b * c + (1 - a) * (1 - b) * (1 - c) =
      1 - a - b - c + a * b + a * c + b * c := by ring

/-- On signs, four times a monochromatic indicator equals one plus pair products. -/
theorem sign_monochromatic_indicator (a b c : ℤ)
    (ha : a = -1 ∨ a = 1) (hb : b = -1 ∨ b = 1) (hc : c = -1 ∨ c = 1) :
    1 + a * b + a * c + b * c = if a = b ∧ b = c then 4 else 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> norm_num

/-- Minimal infeasibility gives a private violation witness for each constraint.
The same statement applies to NAE hyperedges and irreducible infeasible control constraints. -/
theorem private_violation_witness {I X : Type*} (P : I → X → Prop)
    (infeasible : ¬ ∃ x, ∀ i, P i x)
    (critical : ∀ i, ∃ x, ∀ j, j ≠ i → P j x) :
    ∀ i, ∃ x, ¬ P i x ∧ ∀ j, j ≠ i → P j x := by
  classical
  intro i
  obtain ⟨x, hx⟩ := critical i
  refine ⟨x, ?_, hx⟩
  intro hi
  apply infeasible
  refine ⟨x, fun j ↦ ?_⟩
  by_cases hji : j = i
  · simpa [hji] using hi
  · exact hx j hji

/-- Consequently each private witness has exactly one violated constraint.
This is the finite certificate behind the minimum-energy-one observation. -/
theorem singleton_violation_certificate {I X : Type*} [Fintype I] [DecidableEq I]
    (P : I → X → Prop) [∀ i x, Decidable (P i x)]
    (infeasible : ¬ ∃ x, ∀ i, P i x)
    (critical : ∀ i, ∃ x, ∀ j, j ≠ i → P j x) :
    (∀ x, 1 ≤ (Finset.univ.filter (fun i ↦ ¬ P i x)).card) ∧
      ∀ i, ∃ x, Finset.univ.filter (fun j ↦ ¬ P j x) = {i} := by
  classical
  constructor
  · intro x
    have hex : ∃ i, ¬ P i x := by
      by_contra h
      push Not at h
      exact infeasible ⟨x, h⟩
    obtain ⟨i, hi⟩ := hex
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  · intro i
    obtain ⟨x, hi, hx⟩ := private_violation_witness P infeasible critical i
    refine ⟨x, ?_⟩
    ext j
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [hji, hx j hji]

#print axioms recolor
#print axioms triple_constraint
#print axioms vertex_deletion_from_edge_deletion
#print axioms monochromatic_polynomial
#print axioms sign_monochromatic_indicator
#print axioms private_violation_witness
#print axioms singleton_violation_certificate

end Research.HypergraphCertificates
