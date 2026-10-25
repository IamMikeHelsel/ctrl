import Challenge.Erdos834
import ErdosLab.Erdos834.Coloring

/-!
# Erdős Problem 834 (part ii)

There is a 3-uniform hypergraph with weak chromatic number 3, minimum degree at least 7, that
becomes 2-colourable after deleting any edge or any vertex. We use the explicit 9-vertex,
22-edge hypergraph of R. Li (arXiv:2512.24850, Section 4.1), relabelled `1..9 ↦ 0..8`.
Finite witnesses are checked by kernel `decide`. Non-two-colorability uses four
structural contradiction cases, and vertex criticality follows from edge criticality.
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

/-- Normalize color 0 by complementation, then propagate not-all-equal constraints.
Only three binary branch nodes (four leaves) are needed. -/
private theorem liH_not_colorable_two : ¬ liH.HypergraphColorable 2 := by
  have normalized (c : Fin 9 → Fin 2) (h0 : c 0 = 0)
      (hc : liH.IsProperHypergraphColoring c) : False := by
    have edge (a b d : Fin 9) (he : {a, b, d} ∈ liH) :
        ¬ (c a = c b ∧ c b = c d) :=
      Research.HypergraphCertificates.triple_constraint hc he
    by_cases h1 : c 1 = 0
    · have h2 : c 2 = 1 := by
        have := edge 0 1 2 (by unfold liH; decide +kernel)
        omega
      have h8 : c 8 = 1 := by
        have := edge 0 1 8 (by unfold liH; decide +kernel)
        omega
      by_cases h3 : c 3 = 0
      · have h5 : c 5 = 1 := by
          have := edge 0 3 5 (by unfold liH; decide +kernel)
          omega
        have h7 : c 7 = 1 := by
          have := edge 0 3 7 (by unfold liH; decide +kernel)
          omega
        have h4 : c 4 = 0 := by
          have := edge 2 4 7 (by unfold liH; decide +kernel)
          omega
        have h6 : c 6 = 0 := by
          have := edge 2 5 6 (by unfold liH; decide +kernel)
          omega
        exact edge 0 4 6 (by unfold liH; decide +kernel) ⟨by omega, by omega⟩
      · have h3' : c 3 = 1 := by omega
        have h7 : c 7 = 0 := by
          have := edge 2 3 7 (by unfold liH; decide +kernel)
          omega
        have h5 : c 5 = 0 := by
          have := edge 3 5 8 (by unfold liH; decide +kernel)
          omega
        have h4 : c 4 = 1 := by
          have := edge 0 4 7 (by unfold liH; decide +kernel)
          omega
        have h6 : c 6 = 1 := by
          have := edge 0 5 6 (by unfold liH; decide +kernel)
          omega
        exact edge 4 6 8 (by unfold liH; decide +kernel) ⟨by omega, by omega⟩
    · have h1' : c 1 = 1 := by omega
      by_cases h5 : c 5 = 0
      · have h3 : c 3 = 1 := by
          have := edge 0 3 5 (by unfold liH; decide +kernel)
          omega
        have h6 : c 6 = 1 := by
          have := edge 0 5 6 (by unfold liH; decide +kernel)
          omega
        have h2 : c 2 = 0 := by
          have := edge 1 2 6 (by unfold liH; decide +kernel)
          omega
        have h8 : c 8 = 0 := by
          have := edge 1 3 8 (by unfold liH; decide +kernel)
          omega
        have h7 : c 7 = 1 := by
          have := edge 0 2 7 (by unfold liH; decide +kernel)
          omega
        have h4 : c 4 = 1 := by
          have := edge 0 4 8 (by unfold liH; decide +kernel)
          omega
        exact edge 4 6 7 (by unfold liH; decide +kernel) ⟨by omega, by omega⟩
      · have h5' : c 5 = 1 := by omega
        have h2 : c 2 = 0 := by
          have := edge 1 2 5 (by unfold liH; decide +kernel)
          omega
        have h6 : c 6 = 0 := by
          have := edge 1 5 6 (by unfold liH; decide +kernel)
          omega
        have h7 : c 7 = 1 := by
          have := edge 0 2 7 (by unfold liH; decide +kernel)
          omega
        have h4 : c 4 = 1 := by
          have := edge 0 4 6 (by unfold liH; decide +kernel)
          omega
        have h8 : c 8 = 0 := by
          have := edge 1 4 8 (by unfold liH; decide +kernel)
          omega
        have h3 : c 3 = 0 := by
          have := edge 3 5 7 (by unfold liH; decide +kernel)
          omega
        exact edge 0 3 8 (by unfold liH; decide +kernel) ⟨by omega, by omega⟩
  rintro ⟨c, hc⟩
  by_cases h0 : c 0 = 0
  · exact normalized c h0 hc
  · have h0' : c 0 = 1 := by omega
    apply normalized (fun v ↦ Fin.rev (c v))
    · simp [h0', Fin.rev]
    · exact Research.HypergraphCertificates.recolor hc Fin.rev Fin.rev_injective

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

private theorem liH_edge_critical : ∀ e ∈ liH, (liH.erase e).HypergraphColorable 2 := by
  suffices h : ∀ e ∈ liH, ∃ i : Fin 22, (liH.erase e).IsProperHypergraphColoring (edgeWit i) by
    intro e he
    obtain ⟨i, hi⟩ := h e he
    exact ⟨_, hi⟩
  unfold Finset.IsProperHypergraphColoring liH edgeWit
  decide +kernel

private theorem liH_vertex_critical :
    ∀ v : Fin 9, (liH.filter (fun e ↦ v ∉ e)).HypergraphColorable 2 := by
  apply Research.HypergraphCertificates.vertex_deletion_from_edge_deletion liH 2
    liH_edge_critical
  intro v
  have := liH_degree v
  omega

theorem solution : statement :=
  ⟨9, liH, liH_uniform,
    ⟨liH_colorable_three, fun j hj ↦ by
      interval_cases j
      · exact liH_not_colorable_zero
      · exact liH_not_colorable_one
      · exact liH_not_colorable_two⟩,
    liH_edge_critical, liH_vertex_critical, liH_degree⟩

end Challenge.Erdos834
