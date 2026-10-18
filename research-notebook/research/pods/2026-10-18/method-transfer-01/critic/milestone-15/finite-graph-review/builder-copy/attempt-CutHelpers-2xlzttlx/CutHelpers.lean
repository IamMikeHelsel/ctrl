import Erdos128.LowDensityGraph
import Erdos128.WeightedGraph

/-! Attributed extraction from aimir/erdos-128-sparse-halves revision
ba85f319ebb33ec2194ef4c2929a12916329e1e7, LowDensityConstruction.lean.
See extraction.json and CutHelpers.patch for exact ranges and changes. -/

namespace Erdos128
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

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
lemma two_mul_edgeCost_eq_ordered_sum_low
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

lemma edgeCost_eq_neighbor_sum
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


theorem sum_extendLarge (C : OrientedBCLCut G)
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
  have hs : (C.large : Set V).toFinset = C.large := by
    ext v
    simp
  simpa only [largeGraph, edgeCountOn, Finset.card_map, hs] using hmap

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

theorem edgeCost_extendLarge_zeroPotential [Nonempty V]
    (C : OrientedBCLCut G) (π : C.LargeVertex → ℚ) :
    edgeCost G (C.extendLarge π) =
      (C.large.card : ℚ) ^ 2 *
        weightedObjective C.largeGraph C.uniformLargeWeight
          (fun _ ↦ 0) π := by
  classical
  rw [C.edgeCost_extendLarge, C.sq_mul_weightedObjective]
  simp [weightedMean]

theorem sum_eq_card_mul_of_weightedMean [Nonempty V]
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

theorem largeGraph_cliqueFree (C : OrientedBCLCut G)
    (htri : G.CliqueFree 3) : C.largeGraph.CliqueFree 3 := by
  exact htri.comap (SimpleGraph.Embedding.induce (C.large : Set V)).isContained

theorem extendLarge_const (C : OrientedBCLCut G) (q : ℚ) :
    C.extendLarge (fun _ ↦ q) =
      (fun v ↦ q * finsetIndicator C.large v) := by
  funext v
  by_cases hv : v ∈ C.large <;>
    simp [extendLarge, finsetIndicator, hv]



end OrientedBCLCut
end
end Erdos128
