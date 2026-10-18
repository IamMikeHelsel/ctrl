import ReviewClient
open HyperbolicSpinor GUClifford
example : vacuum ((annihilate 2 * annihilate 5) (word [2,5])) = (1 : S7) := by
  rw [reviewerWrongOrder]
  rfl
