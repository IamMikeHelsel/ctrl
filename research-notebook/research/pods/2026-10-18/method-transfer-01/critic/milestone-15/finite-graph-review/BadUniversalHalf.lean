import CriticControls
open Erdos128 Erdos128.FiniteProfileControls
example : ∀ z : Fin 6 → ℚ, IsFractionalHalf z → normalizedEdgeCostQ oneEdge z ≤ 1 / 100 := by
  have h := Erdos128.E9CriticControls.not_every_half_has_endpoint_cost
  simp_all
