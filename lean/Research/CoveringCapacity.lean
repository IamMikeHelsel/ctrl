import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Conditional capacity certificates for exploratory Erdős 273 research

AI-assisted, 2026-10-18. This file proves a finite counting principle and a
concrete arithmetic certificate. Tail and CRT lemmas live in sibling modules;
the complete smooth-family exclusion and original problem are not proved here.
-/

namespace Research.CoveringCapacity

/-- If the total possible coverage inside a surviving set is too small, a point
survives every remaining set. No independence assumption is used. -/
theorem exists_uncovered_of_capacity
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (U : Finset α) (A : ι → Finset α) (b : ι → ℕ)
    (capacity : ∀ i, (U ∩ A i).card ≤ b i)
    (gap : ∑ i, b i < U.card) :
    ∃ x ∈ U, ∀ i, x ∉ A i := by
  classical
  by_contra! h
  have cover : U ⊆ Finset.univ.biUnion (fun i => U ∩ A i) := by
    intro x hx
    obtain ⟨i, hi⟩ := h x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hx, hi⟩⟩
  have bound := Finset.card_biUnion_le (s := Finset.univ) (t := fun i => U ∩ A i)
  have sumBound : ∑ i, (U ∩ A i).card ≤ ∑ i, b i :=
    Finset.sum_le_sum (fun i _ => capacity i)
  have := Finset.card_le_card cover
  omega

def survivors (a : Fin 6) (b : Fin 10) (c : Fin 12) : Finset (Fin 60) :=
  Finset.univ.filter fun x =>
    x.val % 4 ≠ 0 ∧ x.val % 6 ≠ a.val ∧ x.val % 10 ≠ b.val ∧ x.val % 12 ≠ c.val

def fiberCapacity (U : Finset (Fin 60)) (g : ℕ) : ℕ :=
  (Finset.range g).sup fun r => (U.filter fun x => x.val % g = r).card

/-- Coarse upper masses, in thousandths, for the seven nonempty gcd groups.
The mathematical assertion that these bound all 7-smooth prime-minus-one
moduli is deliberately not smuggled into this finite certificate. -/
def scaledRemainderCapacity (U : Finset (Fin 60)) : ℕ :=
  8880 + 480 * fiberCapacity U 4 + 606 * fiberCapacity U 6 +
    210 * fiberCapacity U 10 + 1020 * fiberCapacity U 12

/-- The three large-gcd fibers have uniform sizes at most3,2,1 respectively.
Replacing their maxima by these bounds preserves the certificate margin and
avoids recomputing them for each assignment. -/
theorem large_fibers_bounded (U : Finset (Fin 60)) :
    fiberCapacity U 20 ≤ 3 ∧ fiberCapacity U 30 ≤ 2 ∧ fiberCapacity U 60 ≤ 1 := by
  have mono (g : ℕ) : fiberCapacity U g ≤ fiberCapacity Finset.univ g := by
    unfold fiberCapacity
    apply Finset.sup_le
    intro r hr
    calc
      (U.filter fun x => x.val % g = r).card ≤
          ((Finset.univ : Finset (Fin 60)).filter fun x => x.val % g = r).card := by
        apply Finset.card_le_card
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
      _ ≤ _ := Finset.le_sup (s := Finset.range g)
        (f := fun t => ((Finset.univ : Finset (Fin 60)).filter
          fun x => x.val % g = t).card) hr
  have h20 : fiberCapacity Finset.univ 20 = 3 := by decide +kernel
  have h30 : fiberCapacity Finset.univ 30 = 2 := by decide +kernel
  have h60 : fiberCapacity Finset.univ 60 = 1 := by decide +kernel
  exact ⟨h20 ▸ mono 20, h30 ▸ mono 30, h60 ▸ mono 60⟩

/-- A small-divisor sieve can only discard a composite, including for numbers
too large for trial-division primality testing. -/
theorem prime_passes_divisor_test (m q : ℕ) (hp : (m + 1).Prime) (hq : 1 < q) :
    (m + 1) % q ≠ 0 ∨ m + 1 = q := by
  by_cases h : (m + 1) % q = 0
  · right
    exact ((hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero h)).resolve_left
      (by omega)).symm
  · exact Or.inl h

/-- Exact geometric complement of a∈[1,10], b∈[0,6], c∈[0,4], d∈[0,3].
This is the arithmetic step, not yet a theorem about infinite sums. -/
theorem geometric_tail_arithmetic :
    (35 / 16 : ℚ) - (1023 / 1024) * (1093 / 729) * (781 / 625) * (400 / 343)
      = 632647 / 133358400 ∧
    (632647 / 133358400 : ℚ) < 5 / 1000 := by
  norm_num

/-- Exhaustive arithmetic certificate for all 720 normalized prefix assignments.
All arithmetic is checked by the Lean kernel; no external solver is trusted. -/
theorem seven_smooth_capacity_certificate :
    ∀ a : Fin 6, ∀ b : Fin 10, ∀ c : Fin 12,
      scaledRemainderCapacity (survivors a b c) + 342 ≤
        1000 * (survivors a b c).card := by
  set_option maxRecDepth 4096 in decide +kernel

/-- The numerical certificate produces an actual uncovered point once the
periodic lift size and total remaining capacity have been supplied. Establishing
these hypotheses for a given arithmetic family remains an explicit obligation. -/
theorem uncovered_of_scaled_certificate
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (a : Fin 6) (b : Fin 10) (c : Fin 12) (k : ℕ) (hk : 0 < k)
    (U : Finset α) (A : ι → Finset α)
    (size : U.card = k * (survivors a b c).card)
    (capacity : 1000 * (∑ i, (U ∩ A i).card) ≤
      k * scaledRemainderCapacity (survivors a b c)) :
    ∃ x ∈ U, ∀ i, x ∉ A i := by
  apply exists_uncovered_of_capacity U A (fun i => (U ∩ A i).card)
    (fun _ => le_refl _)
  have h := Nat.mul_le_mul_left k (seven_smooth_capacity_certificate a b c)
  rw [size]
  nlinarith

#print axioms exists_uncovered_of_capacity
#print axioms seven_smooth_capacity_certificate
#print axioms prime_passes_divisor_test
#print axioms geometric_tail_arithmetic
#print axioms large_fibers_bounded
#print axioms uncovered_of_scaled_certificate

end Research.CoveringCapacity
