import Erdos128.LowDensityGraph
import Erdos128.OneStepSaving
import Erdos128.LowDensity

set_option linter.style.header false

/-!
# The finite low-density cut construction

This module carries out the graph-theoretic construction that feeds the
already formalized two-variable low-density optimization.  All profiles and
weights stay rational until the final cast lemma.
-/

namespace Erdos128

open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Rational version of the paper's low-density objective. -/
def lowFQ (a μ : ℚ) : ℚ :=
  min
      (a * (7 / 44 : ℚ) + (1 - a) * (2 / 47 : ℚ) -
        (1 + a) / (4 * (1 - a)) * μ)
      (μ / 4) -
    savingLQ a / (1 - a) ^ 2 * μ ^ 3

theorem savingLQ_eq_lowDensityLQ {a : ℚ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    savingLQ a = min (4 * a ^ 2) (a * (1 - a)) := by
  have hc : centerRadiusQ a = a := by
    unfold centerRadiusQ
    exact min_eq_left (by linarith)
  simp [savingLQ, hc]

/-- Casting the rational objective gives exactly the real objective already
used by `LowDensity.calculus_bound`. -/
theorem lowFQ_cast_eq_LowDensity_F {a μ : ℚ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    (lowFQ a μ : ℝ) = LowDensity.F (a : ℝ) (μ : ℝ) := by
  rw [lowFQ, savingLQ_eq_lowDensityLQ ha0 ha1]
  norm_num [LowDensity.F, LowDensity.B1, LowDensity.P, LowDensity.C,
    LowDensity.L, LowDensity.M0, LowDensity.I0]

private def lowSymEdgeWeight (x : V → ℚ) : Sym2 V → ℚ :=
  Sym2.lift ⟨fun u v ↦ x u * x v, by
    intro u v
    ring⟩

private lemma edgeCost_eq_sum_lowSymEdgeWeight
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) :
    edgeCost G x = ∑ e ∈ G.edgeFinset, lowSymEdgeWeight x e := by
  unfold edgeCost edgeBilin
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      change (x u * x v + x v * x u) / 2 = x u * x v
      ring

/-- The local ordered-sum identity used to compare weighted objectives with
the ambient `edgeCost`. -/
private lemma two_mul_edgeCost_eq_ordered_sum_low
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) :
    2 * edgeCost G x =
      ∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0 := by
  classical
  rw [edgeCost_eq_sum_lowSymEdgeWeight]
  rw [Finset.mul_sum]
  have hfiber :
      ∑ e ∈ G.edgeFinset,
          ∑ d ∈ (Finset.univ.filter fun d : G.Dart ↦ d.edge = e),
            x d.fst * x d.snd =
        ∑ d : G.Dart, x d.fst * x d.snd := by
    exact Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset G.Dart)) (t := G.edgeFinset)
      (g := SimpleGraph.Dart.edge)
      (fun d _ ↦ by simpa using d.edge_mem) _
  calc
    ∑ e ∈ G.edgeFinset, 2 * lowSymEdgeWeight x e =
        ∑ e ∈ G.edgeFinset,
          ∑ d ∈ (Finset.univ.filter fun d : G.Dart ↦ d.edge = e),
            x d.fst * x d.snd := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨u, v⟩ := e
      let d : G.Dart := ⟨(u, v), by simpa using he⟩
      change 2 * lowSymEdgeWeight x s(u, v) =
        ∑ d' ∈ (Finset.univ.filter fun d' : G.Dart ↦ d'.edge = s(u, v)),
          x d'.fst * x d'.snd
      rw [show s(u, v) = d.edge by rfl, d.edge_fiber]
      rw [Finset.sum_pair (Ne.symm d.symm_ne)]
      change 2 * (x u * x v) = x u * x v + x v * x u
      ring
    _ = ∑ d : G.Dart, x d.fst * x d.snd := hfiber
    _ = ∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0 := by
      have hrhs :
          (∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0) =
            ∑ uv : V × V,
              if G.Adj uv.1 uv.2 then x uv.1 * x uv.2 else 0 :=
        (Fintype.sum_prod_type (fun uv : V × V ↦
          if G.Adj uv.1 uv.2 then x uv.1 * x uv.2 else 0)).symm
      rw [hrhs]
      rw [← Finset.sum_filter]
      refine Finset.sum_bij'
        (fun d _ ↦ (d.fst, d.snd))
        (fun uv huv ↦ ⟨uv, (Finset.mem_filter.mp huv).2⟩)
        ?_ ?_ ?_ ?_ ?_
      · intro d hd
        simp
      · intro uv huv
        simp
      · intro d hd
        rfl
      · intro uv huv
        rcases uv with ⟨u, v⟩
        rfl
      · intro d hd
        rfl

private lemma edgeCost_eq_neighbor_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) :
    edgeCost G x =
      (1 / 2 : ℚ) * ∑ u, x u * ∑ v ∈ G.neighborFinset u, x v := by
  classical
  have hordered := two_mul_edgeCost_eq_ordered_sum_low G x
  have hsums :
      (∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0) =
        ∑ u, x u * ∑ v ∈ G.neighborFinset u, x v := by
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum, G.neighborFinset_eq_filter]
    simp [Finset.sum_filter]
  rw [hsums] at hordered
  linarith

private lemma weightedObjective_eq_edgeCost
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : RatProbabilityWeight V) (ψ π : V → ℚ) :
    weightedObjective G W ψ π =
      edgeCost G (fun v ↦ W.weight v * π v) +
        weightedMean W (fun v ↦ ψ v * π v) := by
  classical
  rw [edgeCost_eq_neighbor_sum]
  unfold weightedObjective
  congr 1
  apply congrArg (fun q : ℚ ↦ (1 / 2) * q)
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr
  · ext y
    simp [SimpleGraph.mem_neighborFinset]
  · intro y _
    rfl

private def orderedAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (f g : V → ℚ) : ℚ :=
  ∑ u : V, ∑ v : V, if G.Adj u v then f u * g v else 0

private lemma orderedAdj_comm
    (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℚ) :
    orderedAdj G f g = orderedAdj G g f := by
  classical
  unfold orderedAdj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  by_cases huv : G.Adj u v
  · simp [huv, G.adj_comm, mul_comm]
  · have hvu : ¬ G.Adj v u := by simpa [G.adj_comm] using huv
    simp [huv, hvu]

private lemma orderedAdj_add_expand
    (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℚ) :
    orderedAdj G (fun v ↦ f v + g v) (fun v ↦ f v + g v) =
      orderedAdj G f f + orderedAdj G f g +
        orderedAdj G g f + orderedAdj G g g := by
  classical
  unfold orderedAdj
  rw [show
      (∑ u : V, ∑ v : V,
        if G.Adj u v then (f u + g u) * (f v + g v) else 0) =
      ∑ u : V, ∑ v : V,
        ((if G.Adj u v then f u * f v else 0) +
          (if G.Adj u v then f u * g v else 0) +
          (if G.Adj u v then g u * f v else 0) +
          (if G.Adj u v then g u * g v else 0)) by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : G.Adj u v <;> simp [huv] <;> ring]
  simp only [Finset.sum_add_distrib]

private lemma two_mul_edgeBilin_eq_orderedAdj
    (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℚ) :
    2 * edgeBilin G f g = orderedAdj G f g := by
  have hfg := two_mul_edgeCost_eq_ordered_sum_low G (fun v ↦ f v + g v)
  have hf := two_mul_edgeCost_eq_ordered_sum_low G f
  have hg := two_mul_edgeCost_eq_ordered_sum_low G g
  change 2 * edgeCost G (fun v ↦ f v + g v) =
      orderedAdj G (fun v ↦ f v + g v) (fun v ↦ f v + g v) at hfg
  change 2 * edgeCost G f = orderedAdj G f f at hf
  change 2 * edgeCost G g = orderedAdj G g g at hg
  rw [edgeCost_add, orderedAdj_add_expand] at hfg
  have hcomm := orderedAdj_comm G f g
  linarith

namespace OrientedBCLCut

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Vertices of the large side, as a finite subtype. -/
abbrev LargeVertex (C : OrientedBCLCut G) := {v : V // v ∈ C.large}

/-- The graph induced on the large side. -/
def largeGraph (C : OrientedBCLCut G) : SimpleGraph C.LargeVertex :=
  G.induce (C.large : Set V)

local instance largeVertexFintype (C : OrientedBCLCut G) :
    Fintype C.LargeVertex :=
  Subtype.fintype (fun v ↦ v ∈ C.large)

local instance largeGraphAdjDecidable (C : OrientedBCLCut G) :
    DecidableRel C.largeGraph.Adj :=
  by
    unfold largeGraph
    infer_instance

/-- Uniform strictly positive probability weights on the nonempty large side. -/
def uniformLargeWeight [Nonempty V] (C : OrientedBCLCut G) :
    RatProbabilityWeight C.LargeVertex where
  weight := fun _ ↦ 1 / (C.large.card : ℚ)
  positive := by
    intro y
    have hk : (0 : ℚ) < (C.large.card : ℚ) := by
      exact_mod_cast C.large_nonempty.card_pos
    positivity
  sum_eq_one := by
    have hk : (C.large.card : ℚ) ≠ 0 := by
      exact_mod_cast C.large_nonempty.card_ne_zero
    simp [Fintype.card_coe, hk]

/-- Extend a large-side profile by zero to the ambient vertex type. -/
def extendLarge (C : OrientedBCLCut G) (π : C.LargeVertex → ℚ) : V → ℚ :=
  fun v ↦ if hv : v ∈ C.large then π ⟨v, hv⟩ else 0

/-- Extend a large-side profile by one on the small side. -/
def extendLargeSmallOne (C : OrientedBCLCut G) (π : C.LargeVertex → ℚ) : V → ℚ :=
  fun v ↦ if hv : v ∈ C.large then π ⟨v, hv⟩ else 1

private theorem sum_extendLarge (C : OrientedBCLCut G)
    (π : C.LargeVertex → ℚ) :
    ∑ v, C.extendLarge π v = ∑ y, π y := by
  classical
  calc
    ∑ v, C.extendLarge π v = ∑ v ∈ C.large, C.extendLarge π v := by
      exact (Finset.sum_subset (Finset.subset_univ _) (fun v _ hv ↦ by
        simp [extendLarge, hv])).symm
    _ = ∑ y : C.LargeVertex, C.extendLarge π y :=
      Finset.sum_subtype C.large (fun _ ↦ Iff.rfl) (C.extendLarge π)
    _ = ∑ y, π y := by
      apply Finset.sum_congr rfl
      intro y _
      simp [extendLarge]

private theorem edgeCost_extendLarge (C : OrientedBCLCut G)
    (π : C.LargeVertex → ℚ) :
    edgeCost G (C.extendLarge π) = edgeCost C.largeGraph π := by
  classical
  apply (mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0))
  rw [two_mul_edgeCost_eq_ordered_sum_low,
    two_mul_edgeCost_eq_ordered_sum_low]
  have hinner (y : C.LargeVertex) :
      (∑ v : V, if G.Adj y v then C.extendLarge π v else 0) =
        ∑ z : C.LargeVertex,
          if C.largeGraph.Adj y z then π z else 0 := by
    rw [show (fun v : V ↦ if G.Adj y v then C.extendLarge π v else 0) =
        C.extendLarge (fun z ↦ if C.largeGraph.Adj y z then π z else 0) by
      funext v
      by_cases hv : v ∈ C.large
      · simp [extendLarge, largeGraph, hv]
      · simp [extendLarge, hv]]
    exact C.sum_extendLarge _
  rw [show
      (∑ u : V, ∑ v : V,
        if G.Adj u v then C.extendLarge π u * C.extendLarge π v else 0) =
      ∑ u : V, C.extendLarge π u *
        ∑ v : V, if G.Adj u v then C.extendLarge π v else 0 by
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : G.Adj u v <;> simp [huv]]
  rw [show (fun u : V ↦ C.extendLarge π u *
      ∑ v : V, if G.Adj u v then C.extendLarge π v else 0) =
      C.extendLarge (fun y ↦ π y *
        ∑ z : C.LargeVertex,
          if C.largeGraph.Adj y z then π z else 0) by
    funext u
    by_cases hu : u ∈ C.large
    · simp only [extendLarge, dif_pos hu]
      have hi := hinner (⟨u, hu⟩ : C.LargeVertex)
      simp only [extendLarge] at hi
      rw [hi]
    · simp [extendLarge, hu]]
  rw [C.sum_extendLarge]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hyz : C.largeGraph.Adj y z <;> simp [hyz]

private theorem card_edgeFinset_largeGraph (C : OrientedBCLCut G) :
    C.largeGraph.edgeFinset.card = edgeCountOn G C.large := by
  classical
  have hmap := congrArg Finset.card
    (SimpleGraph.map_edgeFinset_induce
      (s := (C.large : Set V)) (G := G))
  simpa [largeGraph, edgeCountOn] using hmap

theorem edgeMass_uniformLargeWeight [Nonempty V] (C : OrientedBCLCut G) :
    edgeMass C.largeGraph C.uniformLargeWeight = C.mu := by
  classical
  let k : ℚ := C.large.card
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast C.large_nonempty.card_pos
  have hobj := weightedObjective_eq_edgeCost C.largeGraph C.uniformLargeWeight
    (fun _ ↦ 0) (fun _ ↦ 1)
  have hleft :
      weightedObjective C.largeGraph C.uniformLargeWeight
          (fun _ ↦ 0) (fun _ ↦ 1) =
        edgeMass C.largeGraph C.uniformLargeWeight := by
    simp [weightedObjective, edgeMass, weightedMean, weightedDegree]
  rw [hleft] at hobj
  have hweight :
      (fun v : C.LargeVertex ↦ C.uniformLargeWeight.weight v * 1) =
        (fun _ ↦ (1 / k : ℚ)) := by
    funext v
    simp [uniformLargeWeight, k]
  rw [hweight] at hobj
  simp at hobj
  rw [show (fun _ : C.LargeVertex ↦ k⁻¹) =
      (fun v ↦ k⁻¹ * (1 : ℚ)) by funext v; ring,
    edgeCost_smul, edgeCost_one] at hobj
  rw [hobj]
  rw [C.card_edgeFinset_largeGraph]
  unfold mu
  dsimp [k]
  ring

/-- The normalized cross-degree of a large-side vertex into the small side.
This is the linear potential used for the first one-step application. -/
def crossPotential (C : OrientedBCLCut G) (y : C.LargeVertex) : ℚ :=
  (1 / (C.large.card : ℚ)) *
    ∑ u : V, if G.Adj u y then finsetIndicator C.small u else 0

private theorem orderedAdj_small_extendLarge (C : OrientedBCLCut G)
    (π : C.LargeVertex → ℚ) :
    orderedAdj G (finsetIndicator C.small) (C.extendLarge π) =
      ∑ y : C.LargeVertex, π y *
        ∑ u : V, if G.Adj u y then finsetIndicator C.small u else 0 := by
  classical
  unfold orderedAdj
  rw [Finset.sum_comm]
  rw [show
      (∑ v : V, ∑ u : V,
        if G.Adj u v then
          finsetIndicator C.small u * C.extendLarge π v else 0) =
      ∑ v : V, C.extendLarge π v *
        ∑ u : V, if G.Adj u v then finsetIndicator C.small u else 0 by
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases huv : G.Adj u v <;> simp [huv] <;> ring]
  rw [show (fun v : V ↦ C.extendLarge π v *
      ∑ u : V, if G.Adj u v then finsetIndicator C.small u else 0) =
      C.extendLarge (fun y ↦ π y *
        ∑ u : V, if G.Adj u y then finsetIndicator C.small u else 0) by
    funext v
    by_cases hv : v ∈ C.large
    · simp only [extendLarge, dif_pos hv]
    · simp [extendLarge, hv]]
  exact C.sum_extendLarge _

private theorem crossPotential_scaled_mean [Nonempty V]
    (C : OrientedBCLCut G) (π : C.LargeVertex → ℚ) :
    (C.large.card : ℚ) ^ 2 *
        weightedMean C.uniformLargeWeight
          (fun y ↦ C.crossPotential y * π y) =
      orderedAdj G (finsetIndicator C.small) (C.extendLarge π) := by
  classical
  have hk : (C.large.card : ℚ) ≠ 0 := by
    exact_mod_cast C.large_nonempty.card_ne_zero
  rw [C.orderedAdj_small_extendLarge]
  unfold weightedMean crossPotential uniformLargeWeight
  simp only [one_div]
  change (C.large.card : ℚ) ^ 2 *
      ∑ y : C.LargeVertex,
        (C.large.card : ℚ)⁻¹ *
          (((C.large.card : ℚ)⁻¹ *
            (∑ u, if G.Adj u ↑y then finsetIndicator C.small u else 0)) * π y) = _
  have hcancel :
      (C.large.card : ℚ) ^ 2 * (C.large.card : ℚ)⁻¹ ^ 2 = 1 := by
    calc
      _ = ((C.large.card : ℚ) * (C.large.card : ℚ)⁻¹) ^ 2 := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hk]; norm_num
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  calc
    (C.large.card : ℚ) ^ 2 *
          ((C.large.card : ℚ)⁻¹ *
            (((C.large.card : ℚ)⁻¹ *
              (∑ u, if G.Adj u ↑y then finsetIndicator C.small u else 0)) * π y)) =
        ((C.large.card : ℚ) ^ 2 * (C.large.card : ℚ)⁻¹ ^ 2) *
          (π y * ∑ u, if G.Adj u ↑y then finsetIndicator C.small u else 0) := by
      ring
    _ = _ := by rw [hcancel]; ring

private theorem sq_mul_weightedObjective [Nonempty V]
    (C : OrientedBCLCut G) (ψ π : C.LargeVertex → ℚ) :
    (C.large.card : ℚ) ^ 2 *
        weightedObjective C.largeGraph C.uniformLargeWeight ψ π =
      edgeCost C.largeGraph π +
        (C.large.card : ℚ) ^ 2 *
          weightedMean C.uniformLargeWeight (fun y ↦ ψ y * π y) := by
  classical
  let k : ℚ := C.large.card
  have hk : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast C.large_nonempty.card_ne_zero
  rw [weightedObjective_eq_edgeCost]
  have hw :
      (fun y : C.LargeVertex ↦ C.uniformLargeWeight.weight y * π y) =
        (fun y ↦ (1 / k) * π y) := by
    funext y
    simp [uniformLargeWeight, k]
  rw [hw, edgeCost_smul]
  dsimp [k]
  simp only [one_div]
  have hcancel :
      (C.large.card : ℚ) ^ 2 * (C.large.card : ℚ)⁻¹ ^ 2 = 1 := by
    calc
      _ = ((C.large.card : ℚ) * (C.large.card : ℚ)⁻¹) ^ 2 := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hk]; norm_num
  rw [mul_add]
  calc
    (C.large.card : ℚ) ^ 2 *
          ((C.large.card : ℚ)⁻¹ ^ 2 * edgeCost C.largeGraph π) +
        (C.large.card : ℚ) ^ 2 *
          weightedMean C.uniformLargeWeight (fun v ↦ ψ v * π v) =
      ((C.large.card : ℚ) ^ 2 * (C.large.card : ℚ)⁻¹ ^ 2) *
          edgeCost C.largeGraph π +
        (C.large.card : ℚ) ^ 2 *
          weightedMean C.uniformLargeWeight (fun v ↦ ψ v * π v) := by ring
    _ = _ := by rw [hcancel]; ring

/-- Exact ambient cost decomposition for the profile which is one on the
small side and variable on the large side. -/
theorem edgeCost_extendLargeSmallOne [Nonempty V]
    (C : OrientedBCLCut G) (π : C.LargeVertex → ℚ) :
    edgeCost G (C.extendLargeSmallOne π) =
      (edgeCountOn G C.small : ℚ) +
        (C.large.card : ℚ) ^ 2 *
          weightedObjective C.largeGraph C.uniformLargeWeight
            C.crossPotential π := by
  classical
  have hsplit : C.extendLargeSmallOne π =
      (fun v ↦ finsetIndicator C.small v + C.extendLarge π v) := by
    funext v
    by_cases hv : v ∈ C.large
    · have hs : v ∉ C.small := by
        simpa [large] using hv
      simp [extendLargeSmallOne, extendLarge, finsetIndicator, hv, hs]
    · have hs : v ∈ C.small := by
        simpa [large] using hv
      simp [extendLargeSmallOne, extendLarge, finsetIndicator, hv, hs]
  rw [hsplit, edgeCost_add, edgeCost_finsetIndicator,
    C.edgeCost_extendLarge, C.sq_mul_weightedObjective,
    C.crossPotential_scaled_mean, ← two_mul_edgeBilin_eq_orderedAdj]
  ring

/-- Exact ambient cost decomposition for the profile which vanishes on the
small side and is variable on the large side. -/
theorem edgeCost_extendLarge_zeroPotential [Nonempty V]
    (C : OrientedBCLCut G) (π : C.LargeVertex → ℚ) :
    edgeCost G (C.extendLarge π) =
      (C.large.card : ℚ) ^ 2 *
        weightedObjective C.largeGraph C.uniformLargeWeight
          (fun _ ↦ 0) π := by
  classical
  rw [C.edgeCost_extendLarge, C.sq_mul_weightedObjective]
  simp [weightedMean]

private theorem extendLargeSmallOne_eq_add (C : OrientedBCLCut G)
    (π : C.LargeVertex → ℚ) :
    C.extendLargeSmallOne π =
      (fun v ↦ finsetIndicator C.small v + C.extendLarge π v) := by
  funext v
  by_cases hv : v ∈ C.large
  · have hs : v ∉ C.small := by simpa [large] using hv
    simp [extendLargeSmallOne, extendLarge, finsetIndicator, hv, hs]
  · have hs : v ∈ C.small := by simpa [large] using hv
    simp [extendLargeSmallOne, extendLarge, finsetIndicator, hv, hs]

private theorem sum_extendLargeSmallOne (C : OrientedBCLCut G)
    (π : C.LargeVertex → ℚ) :
    ∑ v, C.extendLargeSmallOne π v =
      (C.small.card : ℚ) + ∑ y, π y := by
  classical
  rw [C.extendLargeSmallOne_eq_add, Finset.sum_add_distrib,
    sum_finsetIndicator, C.sum_extendLarge]

private theorem sum_eq_card_mul_of_weightedMean [Nonempty V]
    (C : OrientedBCLCut G) {π : C.LargeVertex → ℚ} {α : ℚ}
    (hmean : weightedMean C.uniformLargeWeight π = α) :
    ∑ y, π y = (C.large.card : ℚ) * α := by
  classical
  have hk : (C.large.card : ℚ) ≠ 0 := by
    exact_mod_cast C.large_nonempty.card_ne_zero
  unfold weightedMean uniformLargeWeight at hmean
  simp only [one_div] at hmean
  rw [← Finset.mul_sum] at hmean
  field_simp [hk] at hmean
  linarith

private theorem isUnit_extendLarge (C : OrientedBCLCut G)
    {π : C.LargeVertex → ℚ} (hπ : IsUnitProfile π) :
    IsUnitProfile (C.extendLarge π) := by
  intro v
  by_cases hv : v ∈ C.large
  · simpa [extendLarge, hv] using hπ ⟨v, hv⟩
  · simp [extendLarge, hv]

private theorem isUnit_extendLargeSmallOne (C : OrientedBCLCut G)
    {π : C.LargeVertex → ℚ} (hπ : IsUnitProfile π) :
    IsUnitProfile (C.extendLargeSmallOne π) := by
  intro v
  by_cases hv : v ∈ C.large
  · simpa [extendLargeSmallOne, hv] using hπ ⟨v, hv⟩
  · simp [extendLargeSmallOne, hv]

/-- A large-side unit profile of weighted mean `a` extends by one to a
fractional half of the ambient graph. -/
theorem isFractionalHalf_extendLargeSmallOne [Nonempty V]
    (C : OrientedBCLCut G) {π : C.LargeVertex → ℚ}
    (hπ : IsUnitProfile π)
    (hmean : weightedMean C.uniformLargeWeight π = C.a) :
    IsFractionalHalf (C.extendLargeSmallOne π) := by
  constructor
  · exact C.isUnit_extendLargeSmallOne hπ
  · rw [C.sum_extendLargeSmallOne,
      C.sum_eq_card_mul_of_weightedMean hmean]
    have hk : (C.large.card : ℚ) ≠ 0 := by
      exact_mod_cast C.large_nonempty.card_ne_zero
    have hcard :
        (C.small.card : ℚ) + (C.large.card : ℚ) =
          (Fintype.card V : ℚ) := by
      exact_mod_cast C.small_card_add_large_card
    unfold a c
    field_simp [hk]
    linarith

/-- A large-side unit profile of weighted mean `c` extends by zero to a
fractional half of the ambient graph. -/
theorem isFractionalHalf_extendLarge [Nonempty V]
    (C : OrientedBCLCut G) {π : C.LargeVertex → ℚ}
    (hπ : IsUnitProfile π)
    (hmean : weightedMean C.uniformLargeWeight π = C.c) :
    IsFractionalHalf (C.extendLarge π) := by
  constructor
  · exact C.isUnit_extendLarge hπ
  · rw [C.sum_extendLarge, C.sum_eq_card_mul_of_weightedMean hmean]
    have hk : (C.large.card : ℚ) ≠ 0 := by
      exact_mod_cast C.large_nonempty.card_ne_zero
    unfold c
    field_simp [hk]

private theorem largeGraph_cliqueFree (C : OrientedBCLCut G)
    (htri : G.CliqueFree 3) : C.largeGraph.CliqueFree 3 := by
  exact htri.comap (SimpleGraph.Embedding.induce (C.large : Set V)).isContained

private theorem extendLarge_const (C : OrientedBCLCut G) (q : ℚ) :
    C.extendLarge (fun _ ↦ q) =
      (fun v ↦ q * finsetIndicator C.large v) := by
  funext v
  by_cases hv : v ∈ C.large <;>
    simp [extendLarge, finsetIndicator, hv]

private theorem extendLargeSmallOne_const (C : OrientedBCLCut G) (q : ℚ) :
    C.extendLargeSmallOne (fun _ ↦ q) =
      (fun v ↦ finsetIndicator C.small v +
        q * finsetIndicator C.large v) := by
  rw [C.extendLargeSmallOne_eq_add, C.extendLarge_const]

private theorem one_eq_small_add_large (C : OrientedBCLCut G) :
    (fun _ : V ↦ (1 : ℚ)) =
      (fun v ↦ finsetIndicator C.small v + finsetIndicator C.large v) := by
  funext v
  by_cases hv : v ∈ C.small
  · have hvl : v ∉ C.large := by simpa [large] using hv
    simp [finsetIndicator, hv, hvl]
  · have hvl : v ∈ C.large := by simpa [large] using hv
    simp [finsetIndicator, hv, hvl]

private theorem edgeCount_partition (C : OrientedBCLCut G) :
    (G.edgeFinset.card : ℚ) =
      (edgeCountOn G C.small : ℚ) +
        2 * edgeBilin G (finsetIndicator C.small)
          (finsetIndicator C.large) +
        (edgeCountOn G C.large : ℚ) := by
  calc
    (G.edgeFinset.card : ℚ) = edgeCost G (fun _ ↦ (1 : ℚ)) :=
      (edgeCost_one G).symm
    _ = edgeCost G (fun v ↦
        finsetIndicator C.small v + finsetIndicator C.large v) := by
      rw [← C.one_eq_small_add_large]
    _ = _ := by
      rw [edgeCost_add, edgeCost_finsetIndicator,
        edgeCost_finsetIndicator]

private theorem baselineOne_edgeCost [Nonempty V]
    (C : OrientedBCLCut G) :
    edgeCost G (C.extendLargeSmallOne (fun _ ↦ C.a)) =
      C.a * (G.edgeFinset.card : ℚ) +
        C.c * ((edgeCountOn G C.small : ℚ) +
          (edgeCountOn G C.large : ℚ)) -
        (1 + C.a) * C.c * (edgeCountOn G C.large : ℚ) := by
  classical
  rw [C.extendLargeSmallOne_const, edgeCost_add,
    edgeCost_finsetIndicator, edgeBilin_smul_right,
    edgeCost_smul, edgeCost_finsetIndicator]
  have hcross :
      2 * edgeBilin G (finsetIndicator C.small)
          (finsetIndicator C.large) =
        (G.edgeFinset.card : ℚ) -
          (edgeCountOn G C.small : ℚ) -
          (edgeCountOn G C.large : ℚ) := by
    linarith [C.edgeCount_partition]
  rw [show 2 * (C.a * edgeBilin G (finsetIndicator C.small)
      (finsetIndicator C.large)) =
      C.a * (2 * edgeBilin G (finsetIndicator C.small)
        (finsetIndicator C.large)) by ring,
    hcross]
  unfold a
  ring

private theorem baselineZero_edgeCost (C : OrientedBCLCut G) :
    edgeCost G (C.extendLarge (fun _ ↦ C.c)) =
      C.c ^ 2 * (edgeCountOn G C.large : ℚ) := by
  rw [C.extendLarge_const, edgeCost_smul,
    edgeCost_finsetIndicator]

private theorem baselineOne_normalized_eq [Nonempty V]
    (C : OrientedBCLCut G) :
    normalizedEdgeCostQ G
        (C.extendLargeSmallOne (fun _ ↦ C.a)) =
      C.a * ((G.edgeFinset.card : ℚ) /
          (Fintype.card V : ℚ) ^ 2) +
        (1 - C.a) *
          (((edgeCountOn G C.small : ℚ) +
              (edgeCountOn G C.large : ℚ)) /
            (Fintype.card V : ℚ) ^ 2) -
        (1 + C.a) / (4 * (1 - C.a)) * C.mu := by
  have hn : (Fintype.card V : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := V)
  have hk : (C.large.card : ℚ) ≠ 0 := by
    exact_mod_cast C.large_nonempty.card_ne_zero
  rw [normalizedEdgeCostQ, C.baselineOne_edgeCost]
  unfold a c mu
  field_simp [hn, hk]
  ring

private theorem baselineZero_normalized_eq [Nonempty V]
    (C : OrientedBCLCut G) :
    normalizedEdgeCostQ G (C.extendLarge (fun _ ↦ C.c)) = C.mu / 4 := by
  have hn : (Fintype.card V : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := V)
  have hk : (C.large.card : ℚ) ≠ 0 := by
    exact_mod_cast C.large_nonempty.card_ne_zero
  rw [normalizedEdgeCostQ, C.baselineZero_edgeCost]
  unfold c mu
  field_simp [hn, hk]
  ring

private theorem baselineOne_normalized_le [Nonempty V]
    (C : OrientedBCLCut G)
    (hdensity : edgeDensityQ G ≤ 7 / 22) :
    normalizedEdgeCostQ G
        (C.extendLargeSmallOne (fun _ ↦ C.a)) ≤
      C.a * (7 / 44) + (1 - C.a) * (2 / 47) -
        (1 + C.a) / (4 * (1 - C.a)) * C.mu := by
  have hn : (0 : ℚ) < (Fintype.card V : ℚ) := by
    exact_mod_cast Fintype.card_pos
  have hM :
      (G.edgeFinset.card : ℚ) / (Fintype.card V : ℚ) ^ 2 ≤ 7 / 44 := by
    unfold edgeDensityQ at hdensity
    calc
      (G.edgeFinset.card : ℚ) / (Fintype.card V : ℚ) ^ 2 =
          (1 / 2 : ℚ) *
            (2 * (G.edgeFinset.card : ℚ) /
              (Fintype.card V : ℚ) ^ 2) := by ring
      _ ≤ (1 / 2 : ℚ) * (7 / 22) :=
        mul_le_mul_of_nonneg_left hdensity (by norm_num)
      _ = 7 / 44 := by norm_num
  have hIraw := C.internal_bound
  push_cast at hIraw
  have hIraw' : (edgeCountOn G C.small : ℚ) +
      (edgeCountOn G C.large : ℚ) ≤
        (2 / 47 : ℚ) * (Fintype.card V : ℚ) ^ 2 := by
    simpa [large] using hIraw
  have hI :
      ((edgeCountOn G C.small : ℚ) +
          (edgeCountOn G C.large : ℚ)) /
          (Fintype.card V : ℚ) ^ 2 ≤ 2 / 47 := by
    rw [div_le_iff₀ (sq_pos_of_pos hn)]
    nlinarith [hIraw']
  rw [C.baselineOne_normalized_eq]
  have ha := C.a_mem_Icc
  have haM := mul_le_mul_of_nonneg_left hM ha.1
  have hcI := mul_le_mul_of_nonneg_left hI (by linarith [ha.2] : 0 ≤ 1 - C.a)
  linarith

private theorem saving_scale [Nonempty V] (C : OrientedBCLCut G) :
    4 * (C.large.card : ℚ) ^ 2 / (Fintype.card V : ℚ) ^ 2 =
      1 / (1 - C.a) ^ 2 := by
  have hn : (Fintype.card V : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := V)
  have hk : (C.large.card : ℚ) ≠ 0 := by
    exact_mod_cast C.large_nonempty.card_ne_zero
  unfold a c
  field_simp [hn, hk]
  ring

private theorem savingLQ_c_eq_a (C : OrientedBCLCut G) :
    savingLQ C.c = savingLQ C.a := by
  have hc : centerRadiusQ C.c = centerRadiusQ C.a := by
    unfold centerRadiusQ a
    rw [show 1 - (1 - C.c) = C.c by ring, min_comm]
  unfold savingLQ
  rw [hc]

private theorem candidateOne_normalized_bound [Nonempty V]
    (C : OrientedBCLCut G) (π : C.LargeVertex → ℚ)
    (hdensity : edgeDensityQ G ≤ 7 / 22)
    (hobj :
      weightedObjective C.largeGraph C.uniformLargeWeight
          C.crossPotential π ≤
        weightedObjective C.largeGraph C.uniformLargeWeight
            C.crossPotential (fun _ ↦ C.a) -
          4 * savingLQ C.a * C.mu ^ 3) :
    normalizedEdgeCostQ G (C.extendLargeSmallOne π) ≤
      C.a * (7 / 44) + (1 - C.a) * (2 / 47) -
        (1 + C.a) / (4 * (1 - C.a)) * C.mu -
        savingLQ C.a / (1 - C.a) ^ 2 * C.mu ^ 3 := by
  have hk2 : 0 ≤ (C.large.card : ℚ) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hobj hk2
  have hamb :
      edgeCost G (C.extendLargeSmallOne π) ≤
        edgeCost G (C.extendLargeSmallOne (fun _ ↦ C.a)) -
          4 * (C.large.card : ℚ) ^ 2 * savingLQ C.a * C.mu ^ 3 := by
    rw [C.edgeCost_extendLargeSmallOne,
      C.edgeCost_extendLargeSmallOne]
    linarith
  have hn2 : 0 ≤ (Fintype.card V : ℚ) ^ 2 := sq_nonneg _
  have hscaled :
      normalizedEdgeCostQ G (C.extendLargeSmallOne π) ≤
        normalizedEdgeCostQ G
            (C.extendLargeSmallOne (fun _ ↦ C.a)) -
          savingLQ C.a / (1 - C.a) ^ 2 * C.mu ^ 3 := by
    unfold normalizedEdgeCostQ
    calc
      edgeCost G (C.extendLargeSmallOne π) /
            (Fintype.card V : ℚ) ^ 2 ≤
          (edgeCost G (C.extendLargeSmallOne (fun _ ↦ C.a)) -
              4 * (C.large.card : ℚ) ^ 2 * savingLQ C.a * C.mu ^ 3) /
            (Fintype.card V : ℚ) ^ 2 :=
        div_le_div_of_nonneg_right hamb hn2
      _ = edgeCost G (C.extendLargeSmallOne (fun _ ↦ C.a)) /
            (Fintype.card V : ℚ) ^ 2 -
          (4 * (C.large.card : ℚ) ^ 2 /
              (Fintype.card V : ℚ) ^ 2) *
            savingLQ C.a * C.mu ^ 3 := by ring
      _ = _ := by rw [C.saving_scale]; ring
  linarith [hscaled, C.baselineOne_normalized_le hdensity]

private theorem candidateZero_normalized_bound [Nonempty V]
    (C : OrientedBCLCut G) (π : C.LargeVertex → ℚ)
    (hobj :
      weightedObjective C.largeGraph C.uniformLargeWeight
          (fun _ ↦ 0) π ≤
        weightedObjective C.largeGraph C.uniformLargeWeight
            (fun _ ↦ 0) (fun _ ↦ C.c) -
          4 * savingLQ C.c * C.mu ^ 3) :
    normalizedEdgeCostQ G (C.extendLarge π) ≤
      C.mu / 4 -
        savingLQ C.a / (1 - C.a) ^ 2 * C.mu ^ 3 := by
  have hk2 : 0 ≤ (C.large.card : ℚ) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hobj hk2
  have hamb :
      edgeCost G (C.extendLarge π) ≤
        edgeCost G (C.extendLarge (fun _ ↦ C.c)) -
          4 * (C.large.card : ℚ) ^ 2 * savingLQ C.a * C.mu ^ 3 := by
    rw [C.edgeCost_extendLarge_zeroPotential,
      C.edgeCost_extendLarge_zeroPotential]
    rw [C.savingLQ_c_eq_a] at hmul
    linarith
  have hn2 : 0 ≤ (Fintype.card V : ℚ) ^ 2 := sq_nonneg _
  unfold normalizedEdgeCostQ
  calc
    edgeCost G (C.extendLarge π) / (Fintype.card V : ℚ) ^ 2 ≤
        (edgeCost G (C.extendLarge (fun _ ↦ C.c)) -
            4 * (C.large.card : ℚ) ^ 2 * savingLQ C.a * C.mu ^ 3) /
          (Fintype.card V : ℚ) ^ 2 :=
      div_le_div_of_nonneg_right hamb hn2
    _ = edgeCost G (C.extendLarge (fun _ ↦ C.c)) /
          (Fintype.card V : ℚ) ^ 2 -
        (4 * (C.large.card : ℚ) ^ 2 /
            (Fintype.card V : ℚ) ^ 2) *
          savingLQ C.a * C.mu ^ 3 := by ring
    _ = C.mu / 4 -
        savingLQ C.a / (1 - C.a) ^ 2 * C.mu ^ 3 := by
      rw [C.saving_scale]
      change normalizedEdgeCostQ G (C.extendLarge (fun _ ↦ C.c)) -
          1 / (1 - C.a) ^ 2 * savingLQ C.a * C.mu ^ 3 = _
      rw [C.baselineZero_normalized_eq]
      ring

end OrientedBCLCut

/-- The low-density branch produces a rational fractional half with exactly
the two-variable objective used by `LowDensity.calculus_bound`. -/
theorem exists_lowDensity_profile
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htri : G.CliqueFree 3)
    (hcut : BCLCutCertificate G)
    (hdensity : edgeDensityQ G ≤ 7 / 22) :
    ∃ (x : V → ℚ) (a μ : ℚ),
      IsFractionalHalf x ∧
        0 ≤ a ∧ a ≤ 1 / 2 ∧
        0 ≤ μ ∧ μ ≤ OrientedBCLCut.capQ a ∧
        normalizedEdgeCostQ G x ≤ lowFQ a μ := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hempty =>
      letI : IsEmpty V := hempty
      refine ⟨fun _ ↦ 0, 0, 0, ?_, by norm_num, by norm_num,
        by norm_num, ?_, ?_⟩
      · constructor
        · intro v
          exact isEmptyElim v
        · simp
      · norm_num [OrientedBCLCut.capQ]
      · norm_num [normalizedEdgeCostQ, lowFQ, savingLQ, centerRadiusQ]
  | inr hnonempty =>
      letI : Nonempty V := hnonempty
      let C : OrientedBCLCut G := Classical.choice (exists_orientedBCLCut G hcut)
      letI : Fintype C.LargeVertex :=
        OrientedBCLCut.largeVertexFintype C
      letI : DecidableRel C.largeGraph.Adj :=
        OrientedBCLCut.largeGraphAdjDecidable C
      have ha := C.a_mem_Icc
      have hc0 : 0 ≤ C.c := C.c_pos.le
      have hc1 : C.c ≤ 1 := C.c_le_one
      have htriY : C.largeGraph.CliqueFree 3 := C.largeGraph_cliqueFree htri
      obtain ⟨πOne, hπOne, hmeanOne, hobjOne⟩ :=
        exists_oneStepSaving C.largeGraph C.uniformLargeWeight htriY
          C.crossPotential C.a ha.1 (ha.2.trans (by norm_num))
      rw [C.edgeMass_uniformLargeWeight] at hobjOne
      obtain ⟨πZero, hπZero, hmeanZero, hobjZero⟩ :=
        exists_oneStepSaving C.largeGraph C.uniformLargeWeight htriY
          (fun _ ↦ 0) C.c hc0 hc1
      rw [C.edgeMass_uniformLargeWeight] at hobjZero
      have hhalfOne :
          IsFractionalHalf (C.extendLargeSmallOne πOne) :=
        C.isFractionalHalf_extendLargeSmallOne hπOne hmeanOne
      have hhalfZero : IsFractionalHalf (C.extendLarge πZero) :=
        C.isFractionalHalf_extendLarge hπZero hmeanZero
      have hcostOne :=
        C.candidateOne_normalized_bound πOne hdensity hobjOne
      have hcostZero := C.candidateZero_normalized_bound πZero hobjZero
      by_cases hchoice :
          C.a * (7 / 44) + (1 - C.a) * (2 / 47) -
              (1 + C.a) / (4 * (1 - C.a)) * C.mu ≤
            C.mu / 4
      · refine ⟨C.extendLargeSmallOne πOne, C.a, C.mu,
          hhalfOne, ha.1, ha.2, C.mu_nonneg, C.mu_le_capQ, ?_⟩
        simpa [lowFQ, min_eq_left hchoice] using hcostOne
      · have hchoice' : C.mu / 4 ≤
            C.a * (7 / 44) + (1 - C.a) * (2 / 47) -
              (1 + C.a) / (4 * (1 - C.a)) * C.mu :=
          le_of_not_ge hchoice
        refine ⟨C.extendLarge πZero, C.a, C.mu,
          hhalfZero, ha.1, ha.2, C.mu_nonneg, C.mu_le_capQ, ?_⟩
        simpa [lowFQ, min_eq_right hchoice'] using hcostZero

end

end Erdos128
