import FiniteControls

namespace Erdos128.E9CriticControls
open FiniteProfileControls

/-- E9's output is existential. Another legal half can cost more than R. -/
theorem expensive_half :
    IsFractionalHalf (finsetIndicator ({0, 1, 2} : Finset (Fin 6))) ∧
      normalizedEdgeCostQ oneEdge (finsetIndicator ({0, 1, 2} : Finset (Fin 6))) = 1 / 36 := by
  constructor
  · apply isFractionalHalf_finsetIndicator; decide
  · rw [normalizedEdgeCostQ, edgeCost_finsetIndicator]
    norm_num [edgeCountOn, oneEdge_edges, Finset.mk_mem_sym2_iff]

theorem not_every_half_has_endpoint_cost :
    ¬ (∀ z : Fin 6 → ℚ, IsFractionalHalf z →
      normalizedEdgeCostQ oneEdge z ≤ 1 / 100) := by
  intro h
  have hc := h _ expensive_half.1
  rw [expensive_half.2] at hc
  norm_num at hc

end Erdos128.E9CriticControls
#print axioms Erdos128.E9CriticControls.expensive_half
#print axioms Erdos128.E9CriticControls.not_every_half_has_endpoint_cost
