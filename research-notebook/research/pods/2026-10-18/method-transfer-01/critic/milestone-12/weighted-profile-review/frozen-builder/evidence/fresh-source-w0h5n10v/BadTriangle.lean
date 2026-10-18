import ProfileControls
open Erdos128 Erdos128.ProfileControls
example : ∃ π : Fin 3 → ℚ, IsUnitProfile π ∧ weightedMean thirds π = 1 / 2 ∧
    weightedObjective triangle thirds (fun _ => 0) π ≤ 0 := by
  have h := triangle_refutes_missing_triangle_free
  simp_all
