import UniquenessClient
open HyperbolicSpinor UniquenessReview
example : (2 : ℝ) • K = K := by
  have h := twice_not_normalized
  simp_all
