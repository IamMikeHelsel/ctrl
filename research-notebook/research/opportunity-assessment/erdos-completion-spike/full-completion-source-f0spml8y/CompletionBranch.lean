import DeletionBridge
set_option maxHeartbeats 1000000

/-! Completion branch 1 for the October 2026 cut/deletion argument.
The ordered-sum helpers below are adapted from aimir/erdos-128-sparse-halves,
LowDensityConstruction.lean at commit ba85f319ebb33ec2194ef4c2929a12916329e1e7.
They are plumbing, not a new graph-theoretic claim. New branch construction
starts at `cross_indicator_eq_degree_sum`.
-/
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private lemma two_mul_edgeCost_eq_ordered_sum_low
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) :
    2 * edgeCost G x =
      ∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0 := by
  classical
  rw [DeletionBridge.edgeCost_eq_sum]
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
    ∑ e ∈ G.edgeFinset, 2 * DeletionBridge.pairWeight x e =
        ∑ e ∈ G.edgeFinset,
          ∑ d ∈ (Finset.univ.filter fun d : G.Dart ↦ d.edge = e),
            x d.fst * x d.snd := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨u, v⟩ := e
      let d : G.Dart := ⟨(u, v), by simpa using he⟩
      change 2 * DeletionBridge.pairWeight x s(u, v) =
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


/-- The cross term counts each edge between the two indicator supports once.
Disjointness is not required for this identity; overlap is counted as ordered
incidences, matching twice the symmetric bilinear form. -/
theorem cross_indicator_eq_degree_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (B E : Finset V) :
    2 * edgeBilin G (finsetIndicator E) (finsetIndicator B) =
      ∑ u ∈ E, ((B.filter fun v => G.Adj u v).card : ℚ) := by
  rw [two_mul_edgeBilin_eq_orderedAdj]
  unfold orderedAdj
  have hinner (u : V) :
      (∑ v : V, if G.Adj u v then finsetIndicator E u * finsetIndicator B v else 0) =
      if u ∈ E then ((B.filter fun v => G.Adj u v).card : ℚ) else 0 := by
    by_cases hu : u ∈ E
    · rw [if_pos hu]
      have hp (v : V) :
          (if G.Adj u v then finsetIndicator E u * finsetIndicator B v else 0) =
          if v ∈ B ∧ G.Adj u v then (1 : ℚ) else 0 := by
        by_cases hv : v ∈ B <;> by_cases ha : G.Adj u v <;>
          simp [finsetIndicator, hu, hv, ha]
      simp_rw [hp]
      simp [Finset.sum_boole, Finset.filter_and]
      congr 1
      ext v
      simp
    · simp [finsetIndicator, hu]
  simp_rw [hinner]
  simp [Finset.sum_filter]

/-- Adding an independent, disjoint set costs exactly its edges into B. -/
theorem independent_extension_cost
    (G : SimpleGraph V) [DecidableRel G.Adj] (B E : Finset V)
    (hdis : Disjoint B E) (hind : G.IsIndepSet (E : Set V)) :
    (edgeCountOn G (B ∪ E) : ℚ) = (edgeCountOn G B : ℚ) +
      ∑ u ∈ E, ((B.filter fun v => G.Adj u v).card : ℚ) := by
  have hi : finsetIndicator (B ∪ E) =
      fun v => finsetIndicator E v + finsetIndicator B v := by
    funext v
    have hnot : ¬ (v ∈ B ∧ v ∈ E) := fun h => Finset.disjoint_left.mp hdis h.1 h.2
    by_cases hb : v ∈ B <;> by_cases he : v ∈ E <;>
      simp_all [finsetIndicator]
  have hz : edgeCost G (finsetIndicator E) = 0 :=
    edgeCost_eq_zero_of_support_subset_indep G hind (by
      intro v hv
      by_contra hn
      have hn' : v ∉ E := hn
      exact hv (by simp [finsetIndicator, hn']))
  rw [← edgeCost_finsetIndicator, hi, edgeCost_add, hz,
    edgeCost_finsetIndicator, cross_indicator_eq_degree_sum]
  ring

/-- Explicit first-branch construction: select m neighbors of one vertex
inside D, append them to B, and bound the resulting induced edge count.
The degree hypothesis is on actual graph incidences into B. -/
theorem exists_neighborhood_completion
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (B D : Finset V) (v : V) (m : ℕ) (q : ℚ)
    (hdis : Disjoint B D)
    (henough : m ≤ (D.filter fun u => G.Adj v u).card)
    (hdegree : ∀ u ∈ D, ((B.filter fun z => G.Adj u z).card : ℚ) ≤ q) :
    ∃ S : Finset V, B ⊆ S ∧ S.card = B.card + m ∧
      (edgeCountOn G S : ℚ) ≤ (edgeCountOn G B : ℚ) + (m : ℚ) * q := by
  obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq henough
  have hED : E ⊆ D := fun u hu => (Finset.mem_filter.mp (hEsub hu)).1
  have hBE : Disjoint B E := hdis.mono_right hED
  have hind : G.IsIndepSet (E : Set V) :=
    (G.isIndepSet_neighborSet_of_triangleFree htri v).mono (by
      intro u hu
      exact (Finset.mem_filter.mp (hEsub hu)).2)
  refine ⟨B ∪ E, Finset.subset_union_left, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hBE, hEcard]
  · rw [independent_extension_cost G B E hBE hind]
    apply add_le_add_right
    calc
      (∑ u ∈ E, ((B.filter fun z => G.Adj u z).card : ℚ)) ≤
          ∑ _u ∈ E, q := Finset.sum_le_sum (fun u hu => hdegree u (hED hu))
      _ = (m : ℚ) * q := by simp [hEcard]

/-- An exact-half specialization directly produces the fractional-half API
required by deletion restoration. There is no completion-existence premise. -/
theorem fractional_half_of_neighborhood_completion
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (B D : Finset V) (v : V) (m : ℕ) (q : ℚ)
    (hdis : Disjoint B D)
    (hhalf : 2 * (B.card + m) = Fintype.card V)
    (henough : m ≤ (D.filter fun u => G.Adj v u).card)
    (hdegree : ∀ u ∈ D, ((B.filter fun z => G.Adj u z).card : ℚ) ≤ q) :
    HasFractionalHalfBound G ((edgeCountOn G B : ℚ) + (m : ℚ) * q) := by
  obtain ⟨S, _hsub, hcard, hcost⟩ :=
    exists_neighborhood_completion G htri B D v m q hdis henough hdegree
  apply hasFractionalHalfBound_of_hasExactSparseHalf G
  exact ⟨S, by omega, hcost⟩

/-- Vertices with more than half of B as neighbors form an independent set.
This proves the structural fact used to choose D in the completion proof. -/
theorem heavy_neighbors_independent
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (B : Finset V) :
    G.IsIndepSet {v | B.card < 2 * (B.filter fun u => G.Adj v u).card} := by
  intro v hv w hw hvw hadj
  have hcommon : ¬ Disjoint (B.filter fun u => G.Adj v u)
      (B.filter fun u => G.Adj w u) := by
    intro hd
    have hc := Finset.card_le_card (show
        (B.filter fun u => G.Adj v u) ∪ (B.filter fun u => G.Adj w u) ⊆ B from
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    rw [Finset.card_union_of_disjoint hd] at hc
    change B.card < 2 * (B.filter fun u => G.Adj v u).card at hv
    change B.card < 2 * (B.filter fun u => G.Adj w u).card at hw
    omega
  obtain ⟨u, huv, huw⟩ := Finset.not_disjoint_iff.mp hcommon
  have hNv : v ∈ G.neighborSet u := (Finset.mem_filter.mp huv).2.symm
  have hNw : w ∈ G.neighborSet u := (Finset.mem_filter.mp huw).2.symm
  exact (G.isIndepSet_neighborSet_of_triangleFree htri u) hNv hNw hvw hadj

/-- Actual construction of the low-degree candidate set D from an upper bound
on independent-set size. It removes B and the heavy-neighbor independent set.
No asserted D-existence or incidence bound appears among the hypotheses. -/
theorem exists_low_degree_candidates
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (B : Finset V) (a : ℕ)
    (hmax : ∀ C : Finset V, G.IsIndepSet (C : Set V) → C.card ≤ a) :
    ∃ D : Finset V, Disjoint B D ∧ D.card = Fintype.card V - a - B.card ∧
      ∀ u ∈ D, ((B.filter fun z => G.Adj u z).card : ℚ) ≤ (B.card : ℚ) / 2 := by
  classical
  let C := Finset.univ.filter fun v : V =>
    v ∉ B ∧ B.card < 2 * (B.filter fun u => G.Adj v u).card
  have hCind : G.IsIndepSet (C : Set V) :=
    (heavy_neighbors_independent G htri B).mono (by
      intro v hv
      exact (Finset.mem_filter.mp hv).2.2)
  have hCcard := hmax C hCind
  have hBC : Disjoint B C := Finset.disjoint_left.mpr (by
    intro v hvB hvC
    exact (Finset.mem_filter.mp hvC).2.1 hvB)
  have hsize : Fintype.card V - a - B.card ≤ (B ∪ C)ᶜ.card := by
    rw [Finset.card_compl, Finset.card_union_of_disjoint hBC]
    omega
  obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq hsize
  refine ⟨D, Finset.disjoint_left.mpr ?_, hDcard, ?_⟩
  · intro v hvB hvD
    have hn := Finset.mem_compl.mp (hDsub hvD)
    exact hn (Finset.mem_union_left C hvB)
  · intro v hvD
    have hn := Finset.mem_compl.mp (hDsub hvD)
    have hnotB : v ∉ B := fun hvB => hn (Finset.mem_union_left C hvB)
    have hnotC : v ∉ C := fun hvC => hn (Finset.mem_union_right B hvC)
    have hle : 2 * (B.filter fun u => G.Adj v u).card ≤ B.card := by
      by_contra h
      have hvC : v ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hnotB, by omega⟩
      exact hnotC hvC
    have hleQ : (2 : ℚ) * ((B.filter fun u => G.Adj v u).card : ℚ) ≤ (B.card : ℚ) :=
      by exact_mod_cast hle
    linarith

/-- Composition with the checked deletion bridge. The hypotheses describe
a real neighborhood completion in the graph after deleting X-internal edges;
the conclusion is a fractional half in the original graph. -/
theorem restore_neighborhood_completion
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (X B D : Finset V) (v : V) (m : ℕ) (q : ℚ)
    (hdis : Disjoint B D)
    (hhalf : 2 * (B.card + m) = Fintype.card V)
    (henough : m ≤ (D.filter fun u => (DeletionBridge.deleteInside G X).Adj v u).card)
    (hdegree : ∀ u ∈ D,
      ((B.filter fun z => (DeletionBridge.deleteInside G X).Adj u z).card : ℚ) ≤ q) :
    HasFractionalHalfBound G
      ((edgeCountOn (DeletionBridge.deleteInside G X) B : ℚ) +
        (m : ℚ) * q + (edgeCountOn G X : ℚ)) := by
  apply DeletionBridge.restore_fractional_half G X
  exact fractional_half_of_neighborhood_completion
    (DeletionBridge.deleteInside G X)
    (DeletionBridge.deleteInside_cliqueFree G X htri)
    B D v m q hdis hhalf henough hdegree

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.cross_indicator_eq_degree_sum
#print axioms Erdos128.CompletionBridge.independent_extension_cost
#print axioms Erdos128.CompletionBridge.exists_neighborhood_completion
#print axioms Erdos128.CompletionBridge.fractional_half_of_neighborhood_completion

#print axioms Erdos128.CompletionBridge.heavy_neighbors_independent
#print axioms Erdos128.CompletionBridge.exists_low_degree_candidates

#print axioms Erdos128.CompletionBridge.restore_neighborhood_completion
