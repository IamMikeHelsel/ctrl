import UniquenessClient
open HyperbolicSpinor UniquenessReview
example : ∀ H : SpinMatrix, VectorCompatible H → H ∅ ∅ = K ∅ ∅ → H = K := by
  have h := zero_coordinate_uniqueness_false
  simp_all
