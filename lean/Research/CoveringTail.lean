import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-! Exact geometric tail for an arbitrary finite set of exponent tuples.
AI-assisted exploratory273 research. The arithmetic-progression bridge is separate. -/

namespace Research.CoveringTail

abbrev Exponents := (ℕ × ℕ) × (ℕ × ℕ)

noncomputable def weight (x : Exponents) : ℝ :=
  ((1 / 2 : ℝ) ^ (x.1.1 + 1) * (1 / 3 : ℝ) ^ x.1.2) *
    ((1 / 5 : ℝ) ^ x.2.1 * (1 / 7 : ℝ) ^ x.2.2)

theorem weight_nonneg (x : Exponents) : 0 ≤ weight x := by
  unfold weight
  positivity

theorem weight_hasSum : HasSum weight (35 / 16) := by
  have h2 : HasSum (fun a : ℕ => (1 / 2 : ℝ) ^ (a + 1)) 1 := by
    simpa only [pow_succ, show (2 : ℝ) * (1 / 2) = 1 by norm_num] using
      hasSum_geometric_two.mul_right (1 / 2 : ℝ)
  have h3 : HasSum (fun b : ℕ => (1 / 3 : ℝ) ^ b) (3 / 2) := by
    convert hasSum_geometric_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h5 : HasSum (fun c : ℕ => (1 / 5 : ℝ) ^ c) (5 / 4) := by
    convert hasSum_geometric_of_lt_one (r := (1 / 5 : ℝ)) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h7 : HasSum (fun d : ℕ => (1 / 7 : ℝ) ^ d) (7 / 6) := by
    convert hasSum_geometric_of_lt_one (r := (1 / 7 : ℝ)) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h23 := h2.mul h3 (h2.summable.mul_of_nonneg h3.summable
    (fun _ => by positivity) (fun _ => by positivity))
  have h57 := h5.mul h7 (h5.summable.mul_of_nonneg h7.summable
    (fun _ => by positivity) (fun _ => by positivity))
  have h := h23.mul h57 (h23.summable.mul_of_nonneg h57.summable
    (fun _ => by positivity) (fun _ => by positivity))
  norm_num at h
  exact h

def box : Finset Exponents :=
  (Finset.range 10 ×ˢ Finset.range 7) ×ˢ (Finset.range 5 ×ˢ Finset.range 4)

theorem box_mass : ∑ x ∈ box, weight x =
    (1023 / 1024 : ℝ) * (1093 / 729) * (781 / 625) * (400 / 343) := by
  simp only [box, weight, Finset.sum_product]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  norm_num [Finset.sum_range_succ]

/-- This applies to EVERY finite subset outside the box, regardless of maximum
exponents. Thus the tail estimate is not a finite cutoff extrapolation. -/
theorem finite_tail_bound (s : Finset Exponents) (h : Disjoint s box) :
    ∑ x ∈ s, weight x ≤ 632647 / 133358400 := by
  have hu : ∑ x ∈ s ∪ box, weight x ≤ 35 / 16 := by
    rw [← weight_hasSum.tsum_eq]
    exact Summable.sum_le_tsum (s ∪ box) (fun _ _ => weight_nonneg _) weight_hasSum.summable
  rw [Finset.sum_union h, box_mass] at hu
  linarith

#print axioms weight_hasSum
#print axioms box_mass
#print axioms finite_tail_bound

end Research.CoveringTail
