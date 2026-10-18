import Erdos128.WeightedGraph

set_option linter.style.header false

/-!
# A cubic neighborhood in a rationally weighted graph

This is the finite rational form of the harmonic-mean argument from the
paper.  It does not require triangle-freeness; that hypothesis enters only
when the selected neighborhood is used as an independent set.
-/

namespace Erdos128

open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V]

theorem weighted_neighbor_sum_swap (H : SimpleGraph V)
    [DecidableEq V] [DecidableRel H.Adj] (a b : V → ℚ) :
    (∑ x, a x * ∑ y ∈ H.neighborFinset x, b y) =
      ∑ y, b y * ∑ x ∈ H.neighborFinset y, a x := by
  classical
  calc
    _ = ∑ x, ∑ y ∈ Finset.univ.filter (H.Adj x), a x * b y := by
      simp_rw [H.neighborFinset_eq_filter, Finset.mul_sum]
    _ = ∑ y, ∑ x ∈ Finset.univ.filter (fun x ↦ H.Adj x y), a x * b y := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ y, b y * ∑ x ∈ H.neighborFinset y, a x := by
      simp_rw [H.neighborFinset_eq_filter, Finset.mul_sum, H.adj_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      ring

private def positiveDegreeVertices (H : SimpleGraph V) (W : RatProbabilityWeight V) : Finset V := by
  classical
  exact Finset.univ.filter fun x ↦ 0 < weightedDegree H W x

private def normalizedDegree (H : SimpleGraph V) (W : RatProbabilityWeight V) (x : V) : ℚ :=
  weightedDegree H W x / (2 * edgeMass H W)

private def neighborhoodHarmonic (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (x : V) : ℚ := by
  classical
  exact (1 / weightedDegree H W x) *
    ∑ y ∈ H.neighborFinset x, W.weight y / normalizedDegree H W y

private def cubicCurve (r : ℚ) : ℚ :=
  2 * r ^ 2 / (r ^ 2 + 1)

private theorem degree_eq_zero_of_not_positive
    (H : SimpleGraph V) (W : RatProbabilityWeight V) {x : V}
    (hx : ¬ 0 < weightedDegree H W x) :
    weightedDegree H W x = 0 := by
  exact le_antisymm (not_lt.mp hx) (weightedDegree_nonneg H W x)

private theorem neighborFinset_nonempty_of_degree_pos
    (H : SimpleGraph V) [DecidableEq V] [DecidableRel H.Adj]
    (W : RatProbabilityWeight V) {x : V}
    (hx : 0 < weightedDegree H W x) :
    (H.neighborFinset x).Nonempty := by
  classical
  by_contra hN
  have hEmpty : H.neighborFinset x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
  have hiso : H.IsIsolated x := (H.neighborFinset_eq_empty x).mp hEmpty
  have hzero : weightedDegree H W x = 0 := by
    simp [weightedDegree, hiso]
  linarith

private theorem normalizedDegree_pos_of_degree_pos
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (hμ : 0 < edgeMass H W) {x : V} (hx : 0 < weightedDegree H W x) :
    0 < normalizedDegree H W x := by
  exact div_pos hx (by positivity)

private theorem normalizedDegree_sum
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (hμ : 0 < edgeMass H W) :
    ∑ x ∈ positiveDegreeVertices H W,
        W.weight x * normalizedDegree H W x = 1 := by
  classical
  let p : ℚ := 2 * edgeMass H W
  have hp : 0 < p := by dsimp [p]; positivity
  have hfull :
      (∑ x, W.weight x * normalizedDegree H W x) = 1 := by
    rw [show (∑ x, W.weight x * normalizedDegree H W x) =
        (∑ x, W.weight x * weightedDegree H W x) / p by
      simp only [normalizedDegree, p]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      ring]
    rw [show (∑ x, W.weight x * weightedDegree H W x) = p by
      simpa [weightedMean, p] using (two_mul_edgeMass H W).symm]
    exact div_self hp.ne'
  rw [← hfull]
  exact Finset.sum_subset (Finset.filter_subset _ _) (fun x _ hx ↦ by
    have hnot : ¬ 0 < weightedDegree H W x := by simpa [positiveDegreeVertices] using hx
    have hzero := degree_eq_zero_of_not_positive H W hnot
    simp [normalizedDegree, hzero])

private theorem positiveDegreeVertices_nonempty
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (hμ : 0 < edgeMass H W) :
    (positiveDegreeVertices H W).Nonempty := by
  classical
  by_contra hs
  have hs0 : positiveDegreeVertices H W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
  have := normalizedDegree_sum H W hμ
  simp [hs0] at this

private theorem activeWeight_le_one
    (H : SimpleGraph V) (W : RatProbabilityWeight V) :
    (∑ x ∈ positiveDegreeVertices H W, W.weight x) ≤ 1 := by
  classical
  calc
    (∑ x ∈ positiveDegreeVertices H W, W.weight x) ≤ ∑ x, W.weight x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ (W.positive _).le)
    _ = 1 := W.sum_eq_one

private theorem cubicCurve_lower (r : ℚ) :
    2 * r - 1 ≤ r * cubicCurve r := by
  have hden : 0 < r ^ 2 + 1 := by nlinarith [sq_nonneg r]
  rw [cubicCurve]
  rw [show r * (2 * r ^ 2 / (r ^ 2 + 1)) = 2 * r ^ 3 / (r ^ 2 + 1) by ring]
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (r - 1)]

private theorem harmonic_average
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (hμ : 0 < edgeMass H W) :
    (∑ x ∈ positiveDegreeVertices H W,
        W.weight x * normalizedDegree H W x * neighborhoodHarmonic H W x) =
      ∑ x ∈ positiveDegreeVertices H W, W.weight x := by
  classical
  let p : ℚ := 2 * edgeMass H W
  let S : Finset V := positiveDegreeVertices H W
  have hp : 0 < p := by dsimp [p]; positivity
  have hterm (x : V) (hx : x ∈ S) :
      W.weight x * normalizedDegree H W x * neighborhoodHarmonic H W x =
        (1 / p) * (W.weight x *
          ∑ y ∈ H.neighborFinset x, W.weight y / normalizedDegree H W y) := by
    have hdx : 0 < weightedDegree H W x := by
      simpa [S, positiveDegreeVertices] using hx
    dsimp [normalizedDegree, neighborhoodHarmonic, p]
    field_simp [hdx.ne', hp.ne']
  calc
    _ = (1 / p) *
        ∑ x ∈ S, W.weight x *
          ∑ y ∈ H.neighborFinset x, W.weight y / normalizedDegree H W y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      exact hterm x hx
    _ = (1 / p) *
        ∑ x, W.weight x *
          ∑ y ∈ H.neighborFinset x, W.weight y / normalizedDegree H W y := by
      apply congrArg (fun q : ℚ ↦ (1 / p) * q)
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun x _ hx ↦ by
        have hnot : ¬ 0 < weightedDegree H W x := by
          simpa [S, positiveDegreeVertices] using hx
        have hdx : weightedDegree H W x = 0 :=
          degree_eq_zero_of_not_positive H W hnot
        have hN : H.neighborFinset x = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          obtain ⟨y, hy⟩ := hne
          have hxy : H.Adj x y := (H.mem_neighborFinset x y).mp hy
          exact hnot (weightedDegree_pos_of_adj H W hxy)
        simp [hN])
    _ = (1 / p) *
        (∑ y, (W.weight y / normalizedDegree H W y) * weightedDegree H W y) := by
      apply congrArg (fun q : ℚ ↦ (1 / p) * q)
      simpa [weightedDegree] using
        (weighted_neighbor_sum_swap H W.weight
          (fun y ↦ W.weight y / normalizedDegree H W y))
    _ = (1 / p) *
        ∑ y ∈ S, (W.weight y / normalizedDegree H W y) * weightedDegree H W y := by
      apply congrArg (fun q : ℚ ↦ (1 / p) * q)
      exact (Finset.sum_subset (Finset.filter_subset _ _) (fun y _ hy ↦ by
        have hnot : ¬ 0 < weightedDegree H W y := by
          simpa [S, positiveDegreeVertices] using hy
        rw [degree_eq_zero_of_not_positive H W hnot]
        simp)).symm
    _ = (1 / p) * ∑ y ∈ S, W.weight y * p := by
      apply congrArg (fun q : ℚ ↦ (1 / p) * q)
      apply Finset.sum_congr rfl
      intro y hy
      have hdy : 0 < weightedDegree H W y := by
        simpa [S, positiveDegreeVertices] using hy
      dsimp [normalizedDegree, p]
      field_simp [hdy.ne', hp.ne']
    _ = ∑ y ∈ S, W.weight y := by
      rw [← Finset.sum_mul]
      field_simp [hp.ne']

private theorem exists_harmonic_control
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (hμ : 0 < edgeMass H W) :
    ∃ x ∈ positiveDegreeVertices H W,
      neighborhoodHarmonic H W x ≤ cubicCurve (normalizedDegree H W x) := by
  classical
  let S : Finset V := positiveDegreeVertices H W
  let A : ℚ := ∑ x ∈ S, W.weight x
  have hsumR := normalizedDegree_sum H W hμ
  have hSne : S.Nonempty := positiveDegreeVertices_nonempty H W hμ
  have hAle : A ≤ 1 := activeWeight_le_one H W
  have hcurve : A ≤
      ∑ x ∈ S, W.weight x * normalizedDegree H W x *
        cubicCurve (normalizedDegree H W x) := by
    have hpoint :
        ∑ x ∈ S, W.weight x * (2 * normalizedDegree H W x - 1) ≤
          ∑ x ∈ S, W.weight x * normalizedDegree H W x *
            cubicCurve (normalizedDegree H W x) := by
      apply Finset.sum_le_sum
      intro x hx
      have hc := cubicCurve_lower (normalizedDegree H W x)
      nlinarith [W.positive x]
    have hleft :
        (∑ x ∈ S, W.weight x * (2 * normalizedDegree H W x - 1)) = 2 - A := by
      rw [show (∑ x ∈ S, W.weight x * (2 * normalizedDegree H W x - 1)) =
          2 * (∑ x ∈ S, W.weight x * normalizedDegree H W x) - A by
        dsimp [A]
        rw [show (∑ x ∈ S, W.weight x * (2 * normalizedDegree H W x - 1)) =
            ∑ x ∈ S, (2 * (W.weight x * normalizedDegree H W x) - W.weight x) by
          apply Finset.sum_congr rfl
          intro x _
          ring]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]]
      simpa [S] using congrArg (fun q : ℚ ↦ 2 * q - A) hsumR
    rw [hleft] at hpoint
    linarith
  by_contra hex
  push Not at hex
  have hstrict :
      (∑ x ∈ S, W.weight x * normalizedDegree H W x *
          cubicCurve (normalizedDegree H W x)) <
        ∑ x ∈ S, W.weight x * normalizedDegree H W x *
          neighborhoodHarmonic H W x := by
    apply Finset.sum_lt_sum
    · intro x hx
      have hcoef : 0 < W.weight x * normalizedDegree H W x :=
        mul_pos (W.positive x)
          (normalizedDegree_pos_of_degree_pos H W hμ
            (by simpa [S, positiveDegreeVertices] using hx))
      exact (mul_lt_mul_of_pos_left (hex x hx) hcoef).le
    · obtain ⟨x, hx⟩ := hSne
      have hcoef : 0 < W.weight x * normalizedDegree H W x :=
        mul_pos (W.positive x)
          (normalizedDegree_pos_of_degree_pos H W hμ
            (by simpa [S, positiveDegreeVertices] using hx))
      exact ⟨x, hx, mul_lt_mul_of_pos_left (hex x hx) hcoef⟩
  have havg := harmonic_average H W hμ
  dsimp [A, S] at hcurve hstrict havg
  linarith

private theorem harmonic_lower
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (hμ : 0 < edgeMass H W) {x : V} (hx : 0 < weightedDegree H W x) :
    (2 * edgeMass H W) * weightedDegree H W x / weightedSecondDegree H W x ≤
      neighborhoodHarmonic H W x := by
  classical
  let p : ℚ := 2 * edgeMass H W
  let d : ℚ := weightedDegree H W x
  let e : ℚ := weightedSecondDegree H W x
  let N : Finset V := H.neighborFinset x
  have hp : 0 < p := by dsimp [p]; positivity
  have hd : 0 < d := by simpa [d] using hx
  have hN : N.Nonempty := by
    simpa [N] using neighborFinset_nonempty_of_degree_pos H W hx
  have hneighbor (y : V) (hy : y ∈ N) : 0 < weightedDegree H W y := by
    have hxy : H.Adj x y := (H.mem_neighborFinset x y).mp (by simpa [N] using hy)
    exact weightedDegree_pos_of_adj H W hxy.symm
  have he : 0 < e := by
    dsimp [e, weightedSecondDegree]
    exact Finset.sum_pos'
      (fun y hy ↦ mul_nonneg (W.positive y).le (weightedDegree_nonneg H W y))
      (by
        obtain ⟨y, hy⟩ := hN
        exact ⟨y, hy, mul_pos (W.positive y) (hneighbor y hy)⟩)
  have hg (y : V) (hy : y ∈ N) :
      0 < W.weight y * normalizedDegree H W y :=
    mul_pos (W.positive y)
      (normalizedDegree_pos_of_degree_pos H W hμ (hneighbor y hy))
  have hcauchy := Finset.sq_sum_div_le_sum_sq_div N W.weight hg
  have hsumw : (∑ y ∈ N, W.weight y) = d := by rfl
  have hsumg :
      (∑ y ∈ N, W.weight y * normalizedDegree H W y) = e / p := by
    dsimp [normalizedDegree, e, p, weightedSecondDegree]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hsumq :
      (∑ y ∈ N, W.weight y ^ 2 /
          (W.weight y * normalizedDegree H W y)) =
        ∑ y ∈ N, W.weight y / normalizedDegree H W y := by
    apply Finset.sum_congr rfl
    intro y hy
    have hw : W.weight y ≠ 0 := (W.positive y).ne'
    have hR : normalizedDegree H W y ≠ 0 :=
      (normalizedDegree_pos_of_degree_pos H W hμ (hneighbor y hy)).ne'
    field_simp [hw, hR]
  rw [hsumw, hsumg, hsumq] at hcauchy
  dsimp [neighborhoodHarmonic]
  have hcauchy' : p * d ^ 2 / e ≤
      ∑ y ∈ N, W.weight y / normalizedDegree H W y := by
    convert hcauchy using 1 <;> field_simp [hp.ne', he.ne']
  calc
    (2 * edgeMass H W) * weightedDegree H W x / weightedSecondDegree H W x =
        (1 / d) * (p * d ^ 2 / e) := by
          dsimp [p, d, e]
          field_simp [hd.ne', he.ne']
    _ ≤ (1 / d) * ∑ y ∈ N, W.weight y / normalizedDegree H W y := by
      exact mul_le_mul_of_nonneg_left hcauchy' (by positivity)
    _ = neighborhoodHarmonic H W x := by rfl

/-- Every positive-edge-mass rationally weighted graph has a positive-degree
vertex whose cubic score is at least `4 μ³`. -/
theorem exists_cubic_neighborhood
    (H : SimpleGraph V) (W : RatProbabilityWeight V)
    (hμ : 0 < edgeMass H W) :
    ∃ x : V, 0 < weightedDegree H W x ∧
      4 * edgeMass H W ^ 3 ≤ cubicScore H W x := by
  classical
  obtain ⟨x, hxS, hharm⟩ := exists_harmonic_control H W hμ
  have hdx : 0 < weightedDegree H W x := by
    simpa [positiveDegreeVertices] using hxS
  have he : 0 < weightedSecondDegree H W x := by
    let N : Finset V := H.neighborFinset x
    have hN : N.Nonempty := by
      simpa [N] using neighborFinset_nonempty_of_degree_pos H W hdx
    dsimp [weightedSecondDegree]
    exact Finset.sum_pos'
      (fun y hy ↦ mul_nonneg (W.positive y).le (weightedDegree_nonneg H W y))
      (by
        obtain ⟨y, hy⟩ := hN
        have hxy : H.Adj x y := (H.mem_neighborFinset x y).mp (by simpa [N] using hy)
        exact ⟨y, by simpa [N] using hy,
          mul_pos (W.positive y) (weightedDegree_pos_of_adj H W hxy.symm)⟩)
  have hlower := harmonic_lower H W hμ hdx
  have hinv :
      (2 * edgeMass H W) * weightedDegree H W x /
          weightedSecondDegree H W x ≤
        cubicCurve (normalizedDegree H W x) := hlower.trans hharm
  let p : ℚ := 2 * edgeMass H W
  let d : ℚ := weightedDegree H W x
  let e : ℚ := weightedSecondDegree H W x
  let R : ℚ := normalizedDegree H W x
  have hp : 0 < p := by dsimp [p]; positivity
  have hd : 0 < d := by simpa [d] using hdx
  have he' : 0 < e := by simpa [e] using he
  have hR : 0 < R := by
    dsimp [R]
    exact normalizedDegree_pos_of_degree_pos H W hμ hdx
  have hden : 0 < R ^ 2 + 1 := by nlinarith [sq_nonneg R]
  have hcross : p * d * (R ^ 2 + 1) ≤ (2 * R ^ 2) * e := by
    apply (div_le_div_iff₀ he' hden).mp
    simpa [p, d, e, R, cubicCurve] using hinv
  have halg : p * (d ^ 2 + p ^ 2) ≤ 2 * e * d := by
    dsimp [R, normalizedDegree] at hcross
    dsimp [p, d, e] at hcross ⊢
    field_simp [hp.ne'] at hcross
    nlinarith
  refine ⟨x, hdx, ?_⟩
  have hpμ : p = 2 * edgeMass H W := rfl
  dsimp [cubicScore]
  dsimp [p, d, e] at halg hpμ
  nlinarith

end

end Erdos128
