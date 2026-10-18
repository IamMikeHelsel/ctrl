import FiniteControls
open Erdos128 Erdos128.FiniteProfileControls
example : IsFractionalHalf (cut.extendLarge (fun _ => (1 / 2 : ℚ))) := by
  have h := wrong_mass.2
  simp_all
