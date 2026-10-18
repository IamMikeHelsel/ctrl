import ReviewClient
open HyperbolicSpinor GUClifford
example : (create 6 * annihilate 6) (1 : S7) = 1 := by
  rw [wrongFactor_vacuum]
  rfl
