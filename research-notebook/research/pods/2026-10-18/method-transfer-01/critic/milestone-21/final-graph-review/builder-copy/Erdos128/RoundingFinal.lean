import Erdos128.RoundingIterate

set_option linter.style.header false

/-!
# Rounding a fractional half to a paper-sized half

This file completes the rounding argument.  Iterated pair rounding leaves at
most one strictly fractional coordinate.  Keeping exactly the coordinates
equal to one then gives `⌊|V| / 2⌋` vertices, including when the graph
order is odd, and cannot increase the edge cost.
-/

namespace Erdos128

open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The indicator of the coordinates equal to one is pointwise at most a
profile taking values in `[0,1]`. -/
private lemma finsetIndicator_ones_le {y : V → ℚ}
    (hy : ∀ v, 0 ≤ y v ∧ y v ≤ 1)
    (S : Finset V) (hS : ∀ v, v ∈ S ↔ y v = 1) :
    ∀ v, finsetIndicator S v ≤ y v := by
  intro v
  by_cases hv : v ∈ S
  · rw [finsetIndicator, if_pos hv, (hS v).mp hv]
  · rw [finsetIndicator, if_neg hv]
    exact (hy v).1

/-- Replacing a nonnegative bounded profile by the indicator of its
one-valued coordinates cannot increase its edge cost. -/
private theorem edgeCost_finsetIndicator_ones_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {y : V → ℚ} (hy : ∀ v, 0 ≤ y v ∧ y v ≤ 1)
    (S : Finset V) (hS : ∀ v, v ∈ S ↔ y v = 1) :
    edgeCost G (finsetIndicator S) ≤ edgeCost G y := by
  have hind_le := finsetIndicator_ones_le hy S hS
  have hind_nonneg : ∀ v, 0 ≤ finsetIndicator S v := by
    intro v
    by_cases hv : v ∈ S <;> simp [finsetIndicator, hv]
  rw [← roundingEdgeCost_eq_edgeCost G (finsetIndicator S),
    ← roundingEdgeCost_eq_edgeCost G y]
  unfold roundingEdgeCost roundingEdgeBilin
  apply Finset.sum_le_sum
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [roundingPairBilin, Sym2.lift_mk]
      have hmul :
          finsetIndicator S u * finsetIndicator S v ≤ y u * y v :=
        mul_le_mul (hind_le u) (hind_le v) (hind_nonneg v) (hy u).1
      linarith

omit [DecidableEq V] in
/-- A bounded profile with at most one non-integral coordinate has total
fractional remainder in `[0,1)`. -/
private lemma nonIntegralRemainder_bounds {y : V → ℚ}
    (hy : ∀ v, 0 ≤ y v ∧ y v ≤ 1)
    (hcard : (nonIntegralCoords y).card ≤ 1) :
    0 ≤ ∑ v ∈ nonIntegralCoords y, y v ∧
      ∑ v ∈ nonIntegralCoords y, y v < 1 := by
  constructor
  · exact Finset.sum_nonneg fun v hv ↦ (hy v).1
  · have hcases : (nonIntegralCoords y).card = 0 ∨
        (nonIntegralCoords y).card = 1 := by omega
    rcases hcases with hzero | hone
    · have hempty : nonIntegralCoords y = ∅ := Finset.card_eq_zero.mp hzero
      simp [hempty]
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hone
      rw [hv, Finset.sum_singleton]
      exact (strict_fractional_of_not_zero_or_one (hy v)
        (mem_nonIntegralCoords.mp (by simp [hv]))).2

/-- Every fractional-half bound rounds to a paper-sized sparse-half bound.
This includes odd graph orders: the unique possible fractional coordinate is
discarded, leaving exactly the floor of half the vertices. -/
theorem hasSparseHalf_of_hasFractionalHalfBound
    (G : SimpleGraph V) [DecidableRel G.Adj] {B : ℚ}
    (h : HasFractionalHalfBound G B) : HasSparseHalf G B := by
  classical
  obtain ⟨x, hx, hxcost⟩ := h
  obtain ⟨y, hy, hysum, hycost, hycard⟩ :=
    exists_rounding_at_most_one G x hx.1
  let S : Finset V := Finset.univ.filter fun v ↦ y v = 1
  let T : Finset V := nonIntegralCoords y
  have hS : ∀ v, v ∈ S ↔ y v = 1 := by
    intro v
    simp [S]
  have hdecomp : ∀ v,
      y v = finsetIndicator S v + if v ∈ T then y v else 0 := by
    intro v
    by_cases hv1 : y v = 1
    · have hvS : v ∈ S := (hS v).mpr hv1
      simp [finsetIndicator, hvS, hv1, T, mem_nonIntegralCoords,
        IsZeroOrOne]
    · have hvS : v ∉ S := by simpa [hS v] using hv1
      by_cases hvT : v ∈ T
      · simp [finsetIndicator, hvS, hvT]
      · have hvIntegral : IsZeroOrOne (y v) := by
          by_contra hnot
          exact hvT (by simpa [T] using (mem_nonIntegralCoords.mpr hnot))
        have hv0 : y v = 0 := hvIntegral.resolve_right hv1
        simp [finsetIndicator, hvS, hvT, hv0]
  have hsum_decomp :
      (∑ v, y v) = (S.card : ℚ) + ∑ v ∈ T, y v := by
    calc
      (∑ v, y v) =
          ∑ v, (finsetIndicator S v + if v ∈ T then y v else 0) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact hdecomp v
      _ = (∑ v, finsetIndicator S v) +
          ∑ v, if v ∈ T then y v else 0 := Finset.sum_add_distrib
      _ = (S.card : ℚ) + ∑ v ∈ T, y v := by
        simp [finsetIndicator]
  have hrem := nonIntegralRemainder_bounds hy (by simpa [T] using hycard)
  have hyhalf : (∑ v, y v) = (Fintype.card V : ℚ) / 2 :=
    hysum.trans hx.2
  have hlowerQ : (2 : ℚ) * (S.card : ℚ) ≤ (Fintype.card V : ℚ) := by
    rw [hsum_decomp] at hyhalf
    linarith [hrem.1]
  have hupperQ : (Fintype.card V : ℚ) <
      (2 : ℚ) * (S.card : ℚ) + 2 := by
    rw [hsum_decomp] at hyhalf
    linarith [hrem.2]
  have hlower : 2 * S.card ≤ Fintype.card V := by
    exact_mod_cast hlowerQ
  have hupper : Fintype.card V < 2 * S.card + 2 := by
    exact_mod_cast hupperQ
  have hScard : S.card = Fintype.card V / 2 := by omega
  refine ⟨S, hScard, ?_⟩
  rw [← edgeCost_finsetIndicator G S]
  exact (edgeCost_finsetIndicator_ones_le G hy S hS).trans
    (hycost.trans hxcost)

end

end Erdos128
