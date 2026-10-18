import SpinClient
open HyperbolicSpinor GUClifford SpinReview
example : ∀ x : Cl, chirality * x = x * chirality := by
  have h := all_commute_is_false
  simp_all
