import ReviewClient
open HyperbolicSpinor GUClifford
example : create 3 (word [0,5]) = word [0,3,5] := by
  rw [reviewerInsertion]
  rfl
