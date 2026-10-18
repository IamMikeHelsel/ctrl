import ComplexUniquenessClient
open HyperbolicSpinor ComplexUniquenessReview
example : ∃ c : ℝ, Complex.I • Kc = (c : ℂ) • Kc := by
  have h := imaginary_not_real_scalar
  simp_all
