import CutHelpers
import SquareCertificate

set_option maxHeartbeats 3000000
namespace Erdos128.FiniteProfileBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def sideMass (C : OrientedBCLCut G) : ℚ :=
  (C.large.card : ℚ) / (Fintype.card V : ℚ)

def sideEdges (C : OrientedBCLCut G) : ℚ :=
  (edgeCountOn G C.large : ℚ) / (Fintype.card V : ℚ) ^ 2

local instance sideFintype (C : OrientedBCLCut G) : Fintype C.LargeVertex :=
  Subtype.fintype (fun v => v ∈ C.large)

local instance sideAdjDecidable (C : OrientedBCLCut G) : DecidableRel C.largeGraph.Adj := by
  unfold OrientedBCLCut.largeGraph
  infer_instance

def sideDegree (C : OrientedBCLCut G) (v : C.LargeVertex) : ℚ :=
  (C.largeGraph.neighborFinset v).card / (Fintype.card V : ℚ)

theorem sideMass_pos [Nonempty V] (C : OrientedBCLCut G) : 0 < sideMass C := by
  unfold sideMass
  have hk : (0 : ℚ) < C.large.card := by exact_mod_cast C.large_nonempty.card_pos
  have hn : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  exact div_pos hk hn

theorem sideMass_le_one [Nonempty V] (C : OrientedBCLCut G) : sideMass C ≤ 1 := by
  have hn : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  unfold sideMass
  apply (div_le_one hn).mpr
  exact_mod_cast C.large_card_le_card

theorem side_alpha [Nonempty V] (C : OrientedBCLCut G) :
    C.c = 1 / (2 * sideMass C) := by
  have hn : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hk : (C.large.card : ℚ) ≠ 0 := by exact_mod_cast C.large_nonempty.card_ne_zero
  unfold OrientedBCLCut.c sideMass
  field_simp [hn, hk]

theorem edge_mass_normalization [Nonempty V] (C : OrientedBCLCut G) :
    edgeMass C.largeGraph C.uniformLargeWeight = sideEdges C / sideMass C ^ 2 := by
  rw [C.edgeMass_uniformLargeWeight]
  have hn : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hk : (C.large.card : ℚ) ≠ 0 := by exact_mod_cast C.large_nonempty.card_ne_zero
  unfold OrientedBCLCut.mu sideEdges sideMass
  field_simp [hn, hk]

theorem degree_normalization [Nonempty V] (C : OrientedBCLCut G) (v : C.LargeVertex) :
    weightedDegree C.largeGraph C.uniformLargeWeight v = sideDegree C v / sideMass C := by
  have hn : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hk : (C.large.card : ℚ) ≠ 0 := by exact_mod_cast C.large_nonempty.card_ne_zero
  unfold weightedDegree OrientedBCLCut.uniformLargeWeight sideDegree sideMass
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp [hn, hk]
  congr 2
  ext w
  simp

theorem normalized_cost_extension [Nonempty V] (C : OrientedBCLCut G)
    (π : C.LargeVertex → ℚ) :
    normalizedEdgeCostQ G (C.extendLarge π) = sideMass C ^ 2 *
      weightedObjective C.largeGraph C.uniformLargeWeight (fun _ => 0) π := by
  rw [normalizedEdgeCostQ, C.edgeCost_extendLarge_zeroPotential]
  unfold sideMass
  ring

theorem mass_extension [Nonempty V] (C : OrientedBCLCut G)
    (π : C.LargeVertex → ℚ) :
    (∑ v, C.extendLarge π v) = (C.large.card : ℚ) * weightedMean C.uniformLargeWeight π := by
  rw [C.sum_extendLarge]
  exact C.sum_eq_card_mul_of_weightedMean rfl

theorem half_from_squared_certificates [Nonempty V]
    (C : OrientedBCLCut G) (htri : G.CliqueFree 3) (R L : ℚ)
    (hy : 1 / 2 < sideMass C) (hR : 0 ≤ R)
    (hA : lowCertificate (sideMass C) (sideEdges C) R L ≤ 0)
    (hH : highCertificate (sideMass C) (sideEdges C) R L ≤ 0) :
    HasNormalizedFractionalHalfBoundQ G R := by
  have ha := alpha_domain (sideMass C) hy
  have hcert := normalized_certificates (sideMass C) (sideEdges C) R L hy hR hA hH
  have hlow : ∀ d : ℚ, 0 ≤ d → d ≤ 1 - 1 / (2 * sideMass C) →
      edgeMass C.largeGraph C.uniformLargeWeight -
        ((R / sideMass C ^ 2) / (1 / (2 * sideMass C)) ^ 2) * (1 - d) ^ 2 - d ^ 2 ≤
        (L / sideMass C) * (d - 2 * edgeMass C.largeGraph C.uniformLargeWeight) := by
    intro d _ _
    simpa only [edge_mass_normalization] using hcert.1 d
  have hhigh : ∀ d : ℚ, 1 - 1 / (2 * sideMass C) < d → d < 1 →
      d * (edgeMass C.largeGraph C.uniformLargeWeight - R / sideMass C ^ 2) /
        (1 - 1 / (2 * sideMass C)) - d ^ 2 ≤
        (L / sideMass C) * (d - 2 * edgeMass C.largeGraph C.uniformLargeWeight) := by
    intro d _ _
    simpa only [edge_mass_normalization] using hcert.2 d
  obtain ⟨π, hunit, hmean, hcost⟩ := ProfileBridge.exists_affine_profile
    C.largeGraph C.uniformLargeWeight (C.largeGraph_cliqueFree htri)
    (1 / (2 * sideMass C)) (R / sideMass C ^ 2) (L / sideMass C)
    ha.1 ha.2 hlow hhigh
  refine ⟨C.extendLarge π, C.isFractionalHalf_extendLarge hunit ?_, ?_⟩
  · simpa only [side_alpha] using hmean
  · rw [normalized_cost_extension]
    calc
      _ ≤ sideMass C ^ 2 * (R / sideMass C ^ 2) :=
        mul_le_mul_of_nonneg_left hcost (sq_nonneg _)
      _ = R := by field_simp [(sideMass_pos C).ne']

end
end Erdos128.FiniteProfileBridge
