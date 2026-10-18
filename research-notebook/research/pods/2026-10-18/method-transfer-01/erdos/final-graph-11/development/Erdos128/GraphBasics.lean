import Mathlib

set_option linter.style.header false

/-!
# Finite graph interfaces for sparse halves

This file supplies the finite-graph definitions used by the formalization.
The quadratic edge cost is written as a sum over unordered edges, so every
edge is counted exactly once.
-/

namespace Erdos128

open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The number of edges of `G` whose two endpoints lie in `S`. -/
def edgeCountOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset ∩ S.sym2).card

/-- The indicator of a finite vertex set, with rational values. -/
def finsetIndicator (S : Finset V) : V → ℚ :=
  fun v ↦ if v ∈ S then 1 else 0

/-- The total mass of a finite-set indicator is its cardinality. -/
theorem sum_finsetIndicator (S : Finset V) :
    ∑ v, finsetIndicator S v = (S.card : ℚ) := by
  simp [finsetIndicator]

/-- The symmetric bilinear contribution of one unordered pair. -/
private def pairBilin (x y : V → ℚ) : Sym2 V → ℚ :=
  Sym2.lift ⟨fun u v ↦ (x u * y v + x v * y u) / 2, by
    intro u v
    ring⟩

/-- The symmetric rational bilinear form obtained by summing over the edges of `G`. -/
def edgeBilin (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V → ℚ) : ℚ :=
  ∑ e ∈ G.edgeFinset, pairBilin x y e

/-- The quadratic edge cost.  For an indicator it is the induced edge count. -/
def edgeCost (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) : ℚ :=
  edgeBilin G x x

/-- A fractional vertex set of total weight exactly half the vertices. -/
def IsFractionalHalf (x : V → ℚ) : Prop :=
  (∀ v, 0 ≤ x v ∧ x v ≤ 1) ∧
    ∑ v, x v = (Fintype.card V : ℚ) / 2

/-- `G` has a fractional half whose edge cost is at most `B`. -/
def HasFractionalHalfBound (G : SimpleGraph V) [DecidableRel G.Adj] (B : ℚ) : Prop :=
  ∃ x : V → ℚ, IsFractionalHalf x ∧ edgeCost G x ≤ B

/-- `G` has a paper-sized half (the floor of half the vertices) with at most
`B` induced edges.  This definition applies uniformly to even and odd graph
orders. -/
def HasSparseHalf (G : SimpleGraph V) [DecidableRel G.Adj] (B : ℚ) : Prop :=
  ∃ S : Finset V,
    S.card = Fintype.card V / 2 ∧ (edgeCountOn G S : ℚ) ≤ B

/-- `G` has an exact half with at most `B` induced edges.

Unlike `HasSparseHalf`, this stronger predicate is false when the graph order
is odd.  It is the hypothesis needed for an indicator to have total rational
weight exactly `Fintype.card V / 2`.
-/
def HasExactSparseHalf (G : SimpleGraph V) [DecidableRel G.Adj] (B : ℚ) : Prop :=
  ∃ S : Finset V,
    2 * S.card = Fintype.card V ∧ (edgeCountOn G S : ℚ) ≤ B

omit [Fintype V] in
private lemma pairBilin_indicator (S : Finset V) (e : Sym2 V) :
    pairBilin (finsetIndicator S) (finsetIndicator S) e =
      if e ∈ S.sym2 then 1 else 0 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [pairBilin, Sym2.lift_mk, finsetIndicator, Finset.mk_mem_sym2_iff]
      by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]

/-- The quadratic cost of an indicator is exactly the induced edge count. -/
theorem edgeCost_finsetIndicator (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    edgeCost G (finsetIndicator S) = (edgeCountOn G S : ℚ) := by
  classical
  simp_rw [edgeCost, edgeBilin, pairBilin_indicator]
  simp only [edgeCountOn, Finset.mem_sym2_iff, Finset.sum_boole, Nat.cast_inj]
  apply congrArg Finset.card
  ext e
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_sym2_iff]

/-- The induced edge count, viewed in the rationals, is nonnegative. -/
lemma edgeCountOn_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (0 : ℚ) ≤ edgeCountOn G S := by
  positivity

omit [DecidableEq V] in
/-- The edge bilinear form is nonnegative on pointwise nonnegative inputs. -/
lemma edgeBilin_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V → ℚ} (hx : ∀ v, 0 ≤ x v) (hy : ∀ v, 0 ≤ y v) :
    0 ≤ edgeBilin G x y := by
  classical
  unfold edgeBilin
  apply Finset.sum_nonneg
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [pairBilin, Sym2.lift_mk]
      exact div_nonneg
        (add_nonneg (mul_nonneg (hx u) (hy v)) (mul_nonneg (hx v) (hy u))) (by norm_num)

omit [DecidableEq V] in
/-- The quadratic edge cost is nonnegative on nonnegative weights. -/
lemma edgeCost_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    {x : V → ℚ} (hx : ∀ v, 0 ≤ x v) :
    0 ≤ edgeCost G x := by
  exact edgeBilin_nonneg G hx hx

omit [DecidableEq V] in
/-- The edge bilinear form is symmetric. -/
lemma edgeBilin_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V → ℚ) :
    edgeBilin G x y = edgeBilin G y x := by
  classical
  unfold edgeBilin
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [pairBilin, Sym2.lift_mk]
      ring

omit [DecidableEq V] in
/-- Additivity in the first argument of the edge bilinear form. -/
lemma edgeBilin_add_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y z : V → ℚ) :
    edgeBilin G (fun v ↦ x v + y v) z =
      edgeBilin G x z + edgeBilin G y z := by
  classical
  unfold edgeBilin
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [pairBilin, Sym2.lift_mk]
      ring

omit [DecidableEq V] in
/-- Additivity in the second argument of the edge bilinear form. -/
lemma edgeBilin_add_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y z : V → ℚ) :
    edgeBilin G x (fun v ↦ y v + z v) =
      edgeBilin G x y + edgeBilin G x z := by
  rw [edgeBilin_comm G x, edgeBilin_add_left, edgeBilin_comm G y,
    edgeBilin_comm G z]

omit [DecidableEq V] in
/-- Scalar multiplication in the first argument of the edge bilinear form. -/
lemma edgeBilin_smul_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℚ) (x y : V → ℚ) :
    edgeBilin G (fun v ↦ c * x v) y = c * edgeBilin G x y := by
  classical
  unfold edgeBilin
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [pairBilin, Sym2.lift_mk]
      ring

omit [DecidableEq V] in
/-- Scalar multiplication in the second argument of the edge bilinear form. -/
lemma edgeBilin_smul_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℚ) (x y : V → ℚ) :
    edgeBilin G x (fun v ↦ c * y v) = c * edgeBilin G x y := by
  rw [edgeBilin_comm G x, edgeBilin_smul_left, edgeBilin_comm G y]

omit [DecidableEq V] in
/-- Quadratic scaling of the edge cost. -/
lemma edgeCost_smul (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℚ) (x : V → ℚ) :
    edgeCost G (fun v ↦ c * x v) = c ^ 2 * edgeCost G x := by
  unfold edgeCost
  rw [edgeBilin_smul_left, edgeBilin_smul_right]
  ring

omit [DecidableEq V] in
/-- Polarization identity for the edge cost. -/
lemma edgeCost_add (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V → ℚ) :
    edgeCost G (fun v ↦ x v + y v) =
      edgeCost G x + 2 * edgeBilin G x y + edgeCost G y := by
  unfold edgeCost
  rw [edgeBilin_add_left, edgeBilin_add_right,
    edgeBilin_add_right, edgeBilin_comm G y x]
  ring

omit [DecidableEq V] in
/-- The all-one profile has cost equal to the number of edges. -/
lemma edgeCost_one (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCost G (fun _ ↦ (1 : ℚ)) = (G.edgeFinset.card : ℚ) := by
  classical
  have hone : (fun _ : V ↦ (1 : ℚ)) =
      finsetIndicator (Finset.univ : Finset V) := by
    funext v
    simp [finsetIndicator]
  rw [hone, edgeCost_finsetIndicator]
  simp [edgeCountOn]

omit [DecidableEq V] in
/-- A profile supported on an independent set has zero edge cost. -/
lemma edgeCost_eq_zero_of_support_subset_indep
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x : V → ℚ} {S : Set V}
    (hS : G.IsIndepSet S)
    (hsupp : ∀ v, x v ≠ 0 → v ∈ S) :
    edgeCost G x = 0 := by
  classical
  unfold edgeCost edgeBilin
  apply Finset.sum_eq_zero
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := by simpa using he
      by_cases hu : x u = 0
      · simp [pairBilin, hu]
      by_cases hv : x v = 0
      · simp [pairBilin, hv]
      exact False.elim ((hS (hsupp u hu) (hsupp v hv) huv.ne) huv)

/-- An exact half has a fractional-half indicator. -/
lemma isFractionalHalf_finsetIndicator {S : Finset V}
    (hcard : 2 * S.card = Fintype.card V) :
    IsFractionalHalf (finsetIndicator S) := by
  constructor
  · intro v
    by_cases hv : v ∈ S <;> simp [finsetIndicator, hv]
  · rw [sum_finsetIndicator]
    have hcardQ : (2 : ℚ) * (S.card : ℚ) = (Fintype.card V : ℚ) := by
      exact_mod_cast hcard
    linarith

/-- Every exact sparse half is a paper-sized sparse half. -/
theorem hasSparseHalf_of_hasExactSparseHalf
    (G : SimpleGraph V) [DecidableRel G.Adj] {B : ℚ}
    (h : HasExactSparseHalf G B) : HasSparseHalf G B := by
  obtain ⟨S, hcard, hcost⟩ := h
  exact ⟨S, by omega, hcost⟩

/-- Every exact sparse half gives the corresponding fractional-half bound. -/
theorem hasFractionalHalfBound_of_hasExactSparseHalf
    (G : SimpleGraph V) [DecidableRel G.Adj] {B : ℚ}
    (h : HasExactSparseHalf G B) : HasFractionalHalfBound G B := by
  obtain ⟨S, hcard, hcost⟩ := h
  exact ⟨finsetIndicator S, isFractionalHalf_finsetIndicator hcard,
    (edgeCost_finsetIndicator G S).trans_le hcost⟩

end

end Erdos128
