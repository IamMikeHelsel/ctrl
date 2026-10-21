import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic
/-! Isolated five-prime extension of the nonnegative geometric-tail proof pattern
in Research/CoveringTail.lean. Original273 sources remain unchanged. -/
noncomputable section
namespace M02ElevenTail
abbrev Exponents := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ

def weight (x : Exponents) : ℝ :=
  (((1/2:ℝ)^(x.1.1.1+1)*(1/3:ℝ)^x.1.1.2) *
    ((1/5:ℝ)^x.1.2.1*(1/7:ℝ)^x.1.2.2)) * (1/11:ℝ)^x.2

theorem weight_nonneg (x : Exponents) : 0 ≤ weight x := by
  unfold weight
  positivity

theorem weight_hasSum : HasSum weight (77/32) := by
  have h2 : HasSum (fun a : ℕ => (1/2:ℝ)^(a+1)) 1 := by
    simpa only [pow_succ, show (2:ℝ)*(1/2)=1 by norm_num] using
      hasSum_geometric_two.mul_right (1/2:ℝ)
  have h3 : HasSum (fun b : ℕ => (1/3:ℝ)^b) (3/2) := by
    convert hasSum_geometric_of_lt_one (r := (1/3:ℝ)) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h5 : HasSum (fun c : ℕ => (1/5:ℝ)^c) (5/4) := by
    convert hasSum_geometric_of_lt_one (r := (1/5:ℝ)) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h7 : HasSum (fun d : ℕ => (1/7:ℝ)^d) (7/6) := by
    convert hasSum_geometric_of_lt_one (r := (1/7:ℝ)) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h11 : HasSum (fun e : ℕ => (1/11:ℝ)^e) (11/10) := by
    convert hasSum_geometric_of_lt_one (r := (1/11:ℝ)) (by norm_num) (by norm_num) using 1 <;> norm_num
  have h23 := h2.mul h3 (h2.summable.mul_of_nonneg h3.summable
    (fun _ => by positivity) (fun _ => by positivity))
  have h57 := h5.mul h7 (h5.summable.mul_of_nonneg h7.summable
    (fun _ => by positivity) (fun _ => by positivity))
  have h2357 := h23.mul h57 (h23.summable.mul_of_nonneg h57.summable
    (fun _ => by positivity) (fun _ => by positivity))
  have h := h2357.mul h11 (h2357.summable.mul_of_nonneg h11.summable
    (fun _ => by positivity) (fun _ => by positivity))
  norm_num at h
  exact h

/-- Exactly checker caps: u=1..14,v=0..9,w=0..6,z=0..5,e=0..4. -/
def box : Finset Exponents :=
  ((Finset.range 14 ×ˢ Finset.range 10) ×ˢ (Finset.range 7 ×ˢ Finset.range 6)) ×ˢ
    Finset.range 5

theorem box_mass : ∑ x ∈ box, weight x =
    (1-(1/2:ℝ)^14)*(3/2)*(1-(1/3:ℝ)^10)*(5/4)*(1-(1/5:ℝ)^7)*
      (7/6)*(1-(1/7:ℝ)^6)*(11/10)*(1-(1/11:ℝ)^5) := by
  simp only [box, weight, Finset.sum_product]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  norm_num [Finset.sum_range_succ]

/-- Every finite set outside the box, with no cap on its exponents. -/
theorem finite_tail_bound (s : Finset Exponents) (h : Disjoint s box) :
    ∑ x ∈ s, weight x ≤ 1806085527193/7116137582400000 := by
  have hu : ∑ x ∈ s ∪ box, weight x ≤ 77/32 := by
    rw [← weight_hasSum.tsum_eq]
    exact Summable.sum_le_tsum (s ∪ box) (fun _ _ => weight_nonneg _) weight_hasSum.summable
  rw [Finset.sum_union h, box_mass] at hu
  norm_num at hu ⊢
  linarith

#print axioms weight_hasSum
#print axioms box_mass
#print axioms finite_tail_bound
end M02ElevenTail
