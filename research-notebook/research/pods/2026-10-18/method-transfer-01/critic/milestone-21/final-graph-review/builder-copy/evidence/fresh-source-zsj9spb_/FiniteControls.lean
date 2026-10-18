import FiniteGraphBridge

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace Erdos128.FiniteProfileControls
open FiniteProfileBridge
open scoped BigOperators

def oneEdge : SimpleGraph (Fin 6) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)
  symm := ⟨by intro u v h; rcases h with h | h <;> simp_all⟩
  loopless := ⟨by intro v h; rcases h with h | h <;> omega⟩

instance : DecidableRel oneEdge.Adj := fun u v =>
  inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)))

theorem oneEdge_edges : oneEdge.edgeFinset = {s(0, 1)} := by decide

theorem oneEdge_triangle_free : oneEdge.CliqueFree 3 := by
  intro s hs
  obtain ⟨u, v, w, huv, huw, hvw, _⟩ := SimpleGraph.is3Clique_iff.mp hs
  change (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) at huv
  change (u = 0 ∧ w = 1) ∨ (u = 1 ∧ w = 0) at huw
  change (v = 0 ∧ w = 1) ∨ (v = 1 ∧ w = 0) at hvw
  rcases huv with huv | huv <;> rcases huw with huw | huw <;>
    rcases hvw with hvw | hvw <;> simp_all

def cut : OrientedBCLCut oneEdge where
  small := {5}
  card_le_compl := by decide
  internal_bound := by
    have hs : edgeCountOn oneEdge ({5} : Finset (Fin 6)) = 0 := by decide
    have hl : edgeCountOn oneEdge ({5} : Finset (Fin 6))ᶜ = 1 := by decide
    rw [hs, hl]
    norm_num

theorem cut_large : cut.large = ({0, 1, 2, 3, 4} : Finset (Fin 6)) := by decide

theorem cut_parameters :
    sideMass cut = 5 / 6 ∧ sideEdges cut = 1 / 36 ∧ cut.c = 3 / 5 := by
  norm_num [sideMass, sideEdges, cut_large, edgeCountOn, oneEdge_edges,
    Finset.mk_mem_sym2_iff, OrientedBCLCut.c]

noncomputable section

theorem local_mass : edgeMass cut.largeGraph cut.uniformLargeWeight = 1 / 25 := by
  rw [edge_mass_normalization, cut_parameters.1, cut_parameters.2.1]
  norm_num

theorem constant_objective :
    weightedObjective cut.largeGraph cut.uniformLargeWeight (fun _ => 0)
      (fun _ => (3 / 5 : ℚ)) = 9 / 625 := by
  have h := ProfileBridge.objective_twoLevel cut.largeGraph cut.uniformLargeWeight
    (cut.largeGraph_cliqueFree oneEdge_triangle_free)
    (⟨0, by rw [cut_large]; simp⟩ : cut.LargeVertex) (3 / 5) 0
  have hp : ProfileBridge.twoLevel cut.largeGraph
      (⟨0, by rw [cut_large]; simp⟩ : cut.LargeVertex) (3 / 5) 0 =
      (fun _ => (3 / 5 : ℚ)) := by
    funext v
    simp [ProfileBridge.twoLevel]
  rw [hp, local_mass] at h
  norm_num at h
  exact h

theorem constant_mass :
    (∑ v, cut.extendLarge (fun _ => (3 / 5 : ℚ)) v) = 3 := by
  rw [mass_extension, weightedMean_const, cut_large]
  norm_num

theorem constant_half_and_cost :
    IsFractionalHalf (cut.extendLarge (fun _ => (3 / 5 : ℚ))) ∧
      normalizedEdgeCostQ oneEdge (cut.extendLarge (fun _ => (3 / 5 : ℚ))) = 1 / 100 := by
  constructor
  · apply cut.isFractionalHalf_extendLarge
    · intro v; norm_num
    · rw [weightedMean_const, cut_parameters.2.2]
  · rw [normalized_cost_extension, constant_objective, cut_parameters.1]
    norm_num

theorem exact_arithmetic_certificate :
    lowCertificate (5 / 6) (1 / 36) (1 / 100) (-1 / 15) = -1 / 5850 ∧
      highCertificate (5 / 6) (1 / 36) (1 / 100) (-1 / 15) = -19 / 22500 := by
  norm_num [lowCertificate, lowCenter, baseSlope, highCertificate, meanDegree]

theorem six_vertex_endpoint : HasNormalizedFractionalHalfBoundQ oneEdge (1 / 100) := by
  apply half_from_squared_certificates cut oneEdge_triangle_free (1 / 100) (-1 / 15)
  · rw [cut_parameters.1]; norm_num
  · norm_num
  · rw [cut_parameters.1, cut_parameters.2.1, exact_arithmetic_certificate.1]; norm_num
  · rw [cut_parameters.1, cut_parameters.2.1, exact_arithmetic_certificate.2]; norm_num

theorem wrong_cost_scale :
    sideMass cut * weightedObjective cut.largeGraph cut.uniformLargeWeight (fun _ => 0)
      (fun _ => (3 / 5 : ℚ)) = 3 / 250 ∧
      sideMass cut * weightedObjective cut.largeGraph cut.uniformLargeWeight (fun _ => 0)
        (fun _ => (3 / 5 : ℚ)) ≠
      normalizedEdgeCostQ oneEdge (cut.extendLarge (fun _ => (3 / 5 : ℚ))) := by
  rw [constant_objective, cut_parameters.1, constant_half_and_cost.2]
  norm_num

theorem wrong_mass :
    (∑ v, cut.extendLarge (fun _ => (1 / 2 : ℚ)) v) = 5 / 2 ∧
      ¬ IsFractionalHalf (cut.extendLarge (fun _ => (1 / 2 : ℚ))) := by
  have hm : (∑ v, cut.extendLarge (fun _ => (1 / 2 : ℚ)) v) = 5 / 2 := by
    rw [mass_extension, weightedMean_const, cut_large]; norm_num
  refine ⟨hm, ?_⟩
  intro h
  have hs := h.2
  rw [hm] at hs
  norm_num at hs

theorem wrong_slope_scale :
    (5 / 6 : ℚ) ^ 2 * (-1 / 15) * ((1 / 6) / (5 / 6) - 2 * ((1 / 36) / (5 / 6) ^ 2)) -
      (-1 / 15) * ((1 / 6) - meanDegree (5 / 6) (1 / 36)) = 1 / 900 := by
  norm_num [meanDegree]

theorem balanced_endpoint_rejected :
    (1 / (2 * (1 / 2 : ℚ))) = 1 ∧
      ¬ (1 / (2 * (1 / 2 : ℚ))) < 1 ∧ (1 / 2 : ℚ) - 1 / 2 = 0 := by
  norm_num

theorem independent_half_zero :
    IsFractionalHalf (finsetIndicator ({2, 3, 4} : Finset (Fin 6))) ∧
      normalizedEdgeCostQ oneEdge (finsetIndicator ({2, 3, 4} : Finset (Fin 6))) = 0 := by
  constructor
  · apply isFractionalHalf_finsetIndicator; decide
  · rw [normalizedEdgeCostQ, edgeCost_finsetIndicator]
    norm_num [edgeCountOn, oneEdge_edges, Finset.mk_mem_sym2_iff]

end
end Erdos128.FiniteProfileControls
