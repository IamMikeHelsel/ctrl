import ComplexFormUniqueness
noncomputable section
namespace ComplexUniquenessReview
open HyperbolicSpinor GUComplex Matrix

theorem Kc_ne_zero : Kc ≠ (0 : CMatrix) := by
  intro h
  have hs := Kc_square
  rw [h, zero_mul] at hs
  exact zero_ne_one hs

theorem imaginary_compatible : ComplexCompatible (Complex.I • Kc) :=
  scalar_complexCompatible Complex.I

theorem imaginary_not_hermitian : (Complex.I • Kc).conjTranspose ≠ Complex.I • Kc := by
  intro h
  have hs : star Complex.I = Complex.I := by
    apply smul_left_injective ℂ Kc_ne_zero
    simpa only [Matrix.conjTranspose_smul, Kc_conjTranspose] using h
  have hi := congrArg Complex.im hs
  norm_num at hi

theorem imaginary_not_real_scalar : ¬ ∃ c : ℝ, Complex.I • Kc = (c : ℂ) • Kc := by
  rintro ⟨c,h⟩
  have hs : Complex.I = (c : ℂ) := smul_left_injective ℂ Kc_ne_zero h
  have hi := congrArg Complex.im hs
  norm_num at hi

theorem zero_is_compatible_hermitian :
    ComplexCompatible (0 : CMatrix) ∧ (0 : CMatrix).conjTranspose = 0 := by
  constructor
  · simpa using scalar_complexCompatible 0
  · simp

end ComplexUniquenessReview
