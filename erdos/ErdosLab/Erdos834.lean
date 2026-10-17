import Challenge.Erdos834

/-!
# Erdős Problem 834 (part ii)

There is a 3-uniform hypergraph with weak chromatic number 3, minimum degree at least 7, that
becomes 2-colourable after deleting any edge or any vertex. We use the explicit 9-vertex,
22-edge hypergraph of R. Li (arXiv:2512.24850, Section 4.1), relabelled `1..9 ↦ 0..8`.
All finite facts are checked by kernel `decide`.
-/

namespace Challenge.Erdos834

open Finset

/-- Li's hypergraph, vertices `0..8`. -/
private def liH : Finset (Finset (Fin 9)) :=
  {{0, 1, 2}, {0, 1, 8}, {0, 2, 7}, {0, 3, 5}, {0, 3, 7}, {0, 3, 8}, {0, 4, 6}, {0, 4, 7},
   {0, 4, 8}, {0, 5, 6}, {1, 2, 5}, {1, 2, 6}, {1, 3, 8}, {1, 4, 8}, {1, 5, 6}, {2, 3, 7},
   {2, 4, 7}, {2, 5, 6}, {3, 5, 7}, {3, 5, 8}, {4, 6, 7}, {4, 6, 8}}

private theorem liH_uniform : liH.IsUniform 3 := by
  unfold Finset.IsUniform liH; decide +kernel

private theorem liH_degree : ∀ v : Fin 9, 7 ≤ liH.hypergraphDegree v := by
  unfold Finset.hypergraphDegree liH; decide +kernel

/-- A proper 3-colouring of `liH`. -/
private theorem liH_colorable_three : liH.HypergraphColorable 3 :=
  ⟨![0, 0, 1, 0, 0, 1, 2, 1, 1], by unfold Finset.IsProperHypergraphColoring liH; decide +kernel⟩

private theorem liH_not_colorable_zero : ¬ liH.HypergraphColorable 0 := by
  rintro ⟨c, -⟩
  exact (c 0).elim0

private theorem liH_not_colorable_one : ¬ liH.HypergraphColorable 1 := by
  rintro ⟨c, hc⟩
  obtain ⟨x, -, y, -, hxy⟩ := hc {0, 1, 2} (by unfold liH; decide +kernel)
  exact hxy (Subsingleton.elim _ _)

/-- No 2-colouring of `liH` is proper: exhaust all `2 ^ 9` colourings. -/
private theorem liH_not_colorable_two : ¬ liH.HypergraphColorable 2 := by
  rintro ⟨c, hc⟩
  revert c
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  unfold Finset.IsProperHypergraphColoring liH
  decide +kernel

/-- Witness 2-colourings: `edgeWit i` is proper on `liH` minus its `i`-th edge. -/
private def edgeWit : Fin 22 → Fin 9 → Fin 2 :=
  ![![0, 0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 1, 1, 0, 0, 1], ![0, 1, 0, 0, 1, 1, 0, 1, 0],
    ![0, 0, 1, 0, 0, 1, 0, 1, 1], ![0, 0, 1, 1, 0, 0, 1, 0, 1], ![0, 1, 0, 1, 0, 0, 1, 1, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 1, 0, 0],
    ![0, 1, 0, 1, 0, 0, 1, 1, 1], ![0, 1, 0, 0, 1, 1, 0, 1, 1], ![0, 1, 0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 1, 1, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 1, 1, 0, 1, 1], ![0, 0, 1, 0, 0, 1, 1, 1, 1],
    ![0, 1, 0, 1, 1, 1, 0, 1, 0], ![0, 0, 1, 1, 1, 1, 0, 0, 1], ![0, 1, 0, 1, 1, 0, 1, 1, 0],
    ![0, 0, 1, 1, 1, 0, 1, 0, 1]]

/-- Witness 2-colourings: `vertWit v` is proper on `liH` minus the vertex `v`. -/
private def vertWit : Fin 9 → Fin 9 → Fin 2 :=
  ![![0, 0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 1, 0, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 0, 1, 0, 1, 1], ![0, 0, 1, 0, 0, 0, 1, 1, 1],
    ![0, 0, 1, 0, 0, 1, 0, 1, 1], ![0, 0, 1, 0, 1, 1, 0, 0, 1], ![0, 0, 1, 1, 1, 0, 1, 0, 0]]

private theorem liH_edge_critical : ∀ e ∈ liH, (liH.erase e).HypergraphColorable 2 := by
  suffices h : ∀ e ∈ liH, ∃ i : Fin 22, (liH.erase e).IsProperHypergraphColoring (edgeWit i) by
    intro e he
    obtain ⟨i, hi⟩ := h e he
    exact ⟨_, hi⟩
  unfold Finset.IsProperHypergraphColoring liH edgeWit
  decide +kernel

private theorem liH_vertex_critical :
    ∀ v : Fin 9, (liH.filter (fun e ↦ v ∉ e)).HypergraphColorable 2 := by
  suffices h : ∀ v : Fin 9, (liH.filter (fun e ↦ v ∉ e)).IsProperHypergraphColoring (vertWit v) by
    exact fun v ↦ ⟨_, h v⟩
  unfold Finset.IsProperHypergraphColoring liH vertWit
  decide +kernel

theorem solution : statement :=
  ⟨9, liH, liH_uniform,
    ⟨liH_colorable_three, fun j hj ↦ by
      interval_cases j
      · exact liH_not_colorable_zero
      · exact liH_not_colorable_one
      · exact liH_not_colorable_two⟩,
    liH_edge_critical, liH_vertex_critical, liH_degree⟩

end Challenge.Erdos834
