import ProfileControls
open Erdos128 Erdos128.ProfileControls
example : ∃ W : RatProbabilityWeight (Fin 2), W.weight = fun _ => 1 := by
  have h := two_unit_masses_not_probability
  simp_all
