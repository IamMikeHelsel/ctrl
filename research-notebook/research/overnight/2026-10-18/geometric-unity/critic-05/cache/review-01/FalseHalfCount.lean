import ReviewerClient
noncomputable section
open Matrix HyperbolicSpinor GUComplex GUClifford
example : (Finset.univ.filter (fun T : Finset J => (0 : J) ∉ T)).card = 63 := by
  rw [positive_half_count]
  norm_num
