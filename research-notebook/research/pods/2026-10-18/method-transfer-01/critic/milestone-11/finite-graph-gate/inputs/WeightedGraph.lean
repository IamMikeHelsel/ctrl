import Mathlib

set_option linter.style.header false

/-!
# Rational probability weights on finite graphs

This file contains the normalization used by the weighted part of the
Erdős--128 argument.  Vertex weights are rational, strictly positive, and
sum to one.  Edge quantities use unordered-edge normalization: equivalently,
they are one half of the corresponding ordered adjacent-pair sum.
-/

namespace Erdos128

open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V]

/-- A strictly positive rational probability weight on a finite type. -/
structure RatProbabilityWeight (V : Type u) [Fintype V] where
  weight : V → ℚ
  positive : ∀ v, 0 < weight v
  sum_eq_one : ∑ v, weight v = 1

/-- A profile whose values lie in the rational unit interval. -/
def IsUnitProfile (π : V → ℚ) : Prop :=
  ∀ v, 0 ≤ π v ∧ π v ≤ 1

/-- Weighted mean of a rational-valued function. -/
def weightedMean (W : RatProbabilityWeight V) (f : V → ℚ) : ℚ :=
  ∑ v, W.weight v * f v

/-- Weighted degree of a vertex. -/
def weightedDegree (H : SimpleGraph V) (W : RatProbabilityWeight V) (x : V) : ℚ := by
  classical
  exact ∑ y ∈ H.neighborFinset x, W.weight y

/-- The weighted average of the degrees in the neighborhood of `x`. -/
def weightedSecondDegree (H : SimpleGraph V) (W : RatProbabilityWeight V) (x : V) : ℚ := by
  classical
  exact ∑ y ∈ H.neighborFinset x, W.weight y * weightedDegree H W y

/-- Weighted edge mass, with every unordered edge counted once. -/
def edgeMass (H : SimpleGraph V) (W : RatProbabilityWeight V) : ℚ :=
  (1 / 2 : ℚ) * weightedMean W (weightedDegree H W)

/-- The cubic score of a neighborhood. -/
def cubicScore (H : SimpleGraph V) (W : RatProbabilityWeight V) (x : V) : ℚ :=
  weightedDegree H W x *
    (weightedSecondDegree H W x - edgeMass H W * weightedDegree H W x)

/-- The quadratic edge objective plus an arbitrary weighted linear term. -/
def weightedObjective (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (ψ π : V → ℚ) : ℚ := by
  classical
  exact
    (1 / 2 : ℚ) *
        (∑ x, W.weight x * π x *
          ∑ y ∈ H.neighborFinset x, W.weight y * π y) +
      weightedMean W (fun x ↦ ψ x * π x)

/-- Distance of `α` from the nearer endpoint of the unit interval. -/
def centerRadiusQ (α : ℚ) : ℚ :=
  min α (1 - α)

/-- The radius product guaranteed by the centered-neighborhood construction. -/
def savingLQ (α : ℚ) : ℚ :=
  min (4 * centerRadiusQ α ^ 2)
    (centerRadiusQ α * (1 - centerRadiusQ α))

@[simp] theorem weightedMean_one (W : RatProbabilityWeight V) :
    weightedMean W (fun _ ↦ 1) = 1 := by
  simp [weightedMean, W.sum_eq_one]

@[simp] theorem weightedMean_const (W : RatProbabilityWeight V) (a : ℚ) :
    weightedMean W (fun _ ↦ a) = a := by
  simp [weightedMean, ← Finset.sum_mul, W.sum_eq_one]

theorem weightedDegree_nonneg (H : SimpleGraph V) (W : RatProbabilityWeight V) (x : V) :
    0 ≤ weightedDegree H W x := by
  classical
  exact Finset.sum_nonneg fun y _ ↦ (W.positive y).le

theorem weightedDegree_pos_of_adj (H : SimpleGraph V) (W : RatProbabilityWeight V)
    {x y : V} (hxy : H.Adj x y) :
    0 < weightedDegree H W x := by
  classical
  unfold weightedDegree
  exact Finset.sum_pos' (fun z _ ↦ (W.positive z).le)
    ⟨y, (H.mem_neighborFinset x y).mpr hxy, W.positive y⟩

theorem weightedDegree_lt_one (H : SimpleGraph V) (W : RatProbabilityWeight V) (x : V) :
    weightedDegree H W x < 1 := by
  classical
  have hsub : H.neighborFinset x ⊆ Finset.univ.erase x := by
    intro y hy
    have hxy : H.Adj x y := (H.mem_neighborFinset x y).mp hy
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact hxy.ne.symm
  have hle : weightedDegree H W x ≤ ∑ y ∈ Finset.univ.erase x, W.weight y := by
    unfold weightedDegree
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ (W.positive _).le)
  have hsplit : W.weight x + ∑ y ∈ Finset.univ.erase x, W.weight y = 1 := by
    exact (Finset.add_sum_erase Finset.univ W.weight (Finset.mem_univ x)).trans W.sum_eq_one
  linarith [W.positive x]

theorem edgeMass_nonneg (H : SimpleGraph V) (W : RatProbabilityWeight V) :
    0 ≤ edgeMass H W := by
  unfold edgeMass weightedMean
  apply mul_nonneg
  · norm_num
  · exact Finset.sum_nonneg fun x _ ↦
      mul_nonneg (W.positive x).le (weightedDegree_nonneg H W x)

theorem weightedSecondDegree_nonneg
    (H : SimpleGraph V) (W : RatProbabilityWeight V) (x : V) :
    0 ≤ weightedSecondDegree H W x := by
  classical
  unfold weightedSecondDegree
  exact Finset.sum_nonneg fun y _ ↦
    mul_nonneg (W.positive y).le (weightedDegree_nonneg H W y)

theorem two_mul_edgeMass (H : SimpleGraph V) (W : RatProbabilityWeight V) :
    2 * edgeMass H W = weightedMean W (weightedDegree H W) := by
  unfold edgeMass
  ring

theorem weightedMean_eq_sum_filter (W : RatProbabilityWeight V) (f : V → ℚ)
    (P : V → Prop) [DecidablePred P] (hf : ∀ x, ¬ P x → f x = 0) :
    weightedMean W f = ∑ x ∈ Finset.univ.filter P, W.weight x * f x := by
  classical
  unfold weightedMean
  exact (Finset.sum_subset (Finset.filter_subset P Finset.univ) (fun x _ hx ↦ by
    have hnP : ¬ P x := by simpa using hx
    simp [hf x hnP])).symm

end

end Erdos128
