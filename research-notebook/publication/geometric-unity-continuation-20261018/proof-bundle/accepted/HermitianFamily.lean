import ComplexChoices
import ComplexBridge
import SpinEquivariance
noncomputable section
namespace HyperbolicSpinor
open GUClifford GUComplex

def W : CMatrix := complexMatrixEquiv imaginaryVolume

theorem imaginaryVolume_bar : bar imaginaryVolume = imaginaryVolume := by
  rw [imaginaryVolume, bar_I_smul, complexVolume_bar, smul_neg, neg_smul, neg_neg]

theorem W_square : W * W = -1 := by
  rw [W, ← map_mul, imaginaryVolume_square, map_neg, map_one]

theorem W_adjoint : Kc * W.conjTranspose * Kc = W := by
  rw [W, ← complexMatrixEquiv_bar, imaginaryVolume_bar]

theorem W_form_selfadjoint : W.conjTranspose * Kc = Kc * W := by
  have h := congrArg (fun A : CMatrix => Kc*A) W_adjoint
  simpa only [← mul_assoc, Kc_square, one_mul] using h

def hermitianFamily (t : ℝ) : CMatrix := Kc * (1 + (t : ℂ) • W)
def hermitianFamilyInverse (t : ℝ) : CMatrix :=
  (((1+(t:ℂ)^2)⁻¹) • (1-(t:ℂ) • W)) * Kc

theorem hermitianFamily_hermitian (t : ℝ) :
    (hermitianFamily t).conjTranspose = hermitianFamily t := by
  simp only [hermitianFamily, Matrix.conjTranspose_mul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul, Kc_conjTranspose,
    Complex.star_def, Complex.conj_ofReal, add_mul, one_mul, smul_mul_assoc,
    W_form_selfadjoint, mul_add, mul_one, mul_smul_comm]

theorem factor_product (t : ℝ) :
    (1+(t:ℂ) • W) * (1-(t:ℂ) • W) = (1+(t:ℂ)^2) • (1:CMatrix) := by
  simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul, smul_add, smul_sub, W_square, smul_neg, sub_neg_eq_add, pow_two, add_smul, one_smul]
  abel

theorem factor_product_reverse (t : ℝ) :
    (1-(t:ℂ) • W) * (1+(t:ℂ) • W) = (1+(t:ℂ)^2) • (1:CMatrix) := by
  simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul, smul_add, smul_sub, W_square, smul_neg, sub_neg_eq_add, pow_two, add_smul, one_smul]
  abel

theorem denominator_ne_zero (t : ℝ) : (1+(t:ℂ)^2) ≠ 0 := by
  have h : (1+t^2 : ℝ) ≠ 0 := by nlinarith [sq_nonneg t]
  exact_mod_cast h

theorem hermitianFamily_inverse_right (t : ℝ) :
    hermitianFamily t * hermitianFamilyInverse t = 1 := by
  simp only [hermitianFamily, hermitianFamilyInverse, mul_smul_comm, smul_mul_assoc]
  rw [mul_assoc Kc, ← mul_assoc (1+(t:ℂ) • W), factor_product]
  simp only [mul_smul_comm, smul_mul_assoc, one_mul, Kc_square, smul_smul]
  rw [inv_mul_cancel₀ (denominator_ne_zero t), one_smul]

theorem hermitianFamily_inverse_left (t : ℝ) :
    hermitianFamilyInverse t * hermitianFamily t = 1 := by
  simp only [hermitianFamily, hermitianFamilyInverse, smul_mul_assoc]
  rw [mul_assoc, ← mul_assoc Kc, Kc_square, one_mul, factor_product_reverse,
    smul_smul, inv_mul_cancel₀ (denominator_ne_zero t), one_smul]

/-- The matrix of the actual real Spin element after complex scalar extension. -/
def spinMatrix (s : spinGroup Q) : CMatrix := complexMatrixEquiv (embed (s : Cl))

theorem spinMatrix_K_unitary (s : spinGroup Q) :
    (spinMatrix s).conjTranspose * Kc * spinMatrix s = Kc := by
  have h : Kc * (spinMatrix s).conjTranspose * Kc * spinMatrix s = 1 := by
    rw [spinMatrix, ← complexMatrixEquiv_bar, ← map_mul, bar_embed, ← map_mul,
      spinGroup.star_mul_self_of_mem s.property, map_one, map_one]
  have hh := congrArg (fun A : CMatrix => Kc*A) h
  simpa only [← mul_assoc, Kc_square, one_mul, mul_one] using hh

theorem W_commutes_spinMatrix (s : spinGroup Q) : W * spinMatrix s = spinMatrix s * W := by
  dsimp [W, spinMatrix, imaginaryVolume, complexVolume]
  rw [← map_mul, ← map_mul, smul_mul_assoc, mul_smul_comm, ← map_mul, ← map_mul,
    chirality_commutes_spin _ s.property]

theorem hermitianFamily_spin_invariant (s : spinGroup Q) (t : ℝ) :
    (spinMatrix s).conjTranspose * hermitianFamily t * spinMatrix s = hermitianFamily t := by
  have hf : (1+(t:ℂ) • W) * spinMatrix s = spinMatrix s * (1+(t:ℂ) • W) := by
    simp only [add_mul, one_mul, smul_mul_assoc, W_commutes_spinMatrix,
      mul_add, mul_one, mul_smul_comm]
  unfold hermitianFamily
  calc
    _ = (spinMatrix s).conjTranspose * Kc * ((1+(t:ℂ) • W)*spinMatrix s) := by simp only [mul_assoc]
    _ = _ := by rw [hf, ← mul_assoc, spinMatrix_K_unitary]

theorem imaginaryVolume_anticommutes_zero :
    imaginaryVolume * cgamma 0 = -(cgamma 0 * imaginaryVolume) := by
  dsimp [imaginaryVolume, complexVolume, cgamma]
  rw [smul_mul_assoc, mul_smul_comm, ← map_mul, ← map_mul,
    chirality_anticommutes_gamma, map_neg, smul_neg]

theorem imaginaryVolume_not_complex_scalar (c : ℂ) :
    imaginaryVolume ≠ c • (1 : CCl) := by
  intro h
  have ha := imaginaryVolume_anticommutes_zero
  rw [h] at ha
  have hb := congrArg (fun x : CCl => x * cgamma 0) ha
  simp only [smul_mul_assoc, one_mul, mul_smul_comm, mul_one, neg_mul,
    cgamma_zero_sq] at hb
  have hb' : c • (1 : CCl) = (-c) • (1 : CCl) := by
    calc
      _ = -(c • cgamma 0) * cgamma 0 := hb
      _ = ((-c) • cgamma 0) * cgamma 0 := by rw [neg_smul]
      _ = _ := by rw [smul_mul_assoc, cgamma_zero_sq]
  have hc : c = -c := (smul_left_injective ℂ (one_ne_zero : (1 : CCl) ≠ 0)) hb' 
  have hz : c = 0 := by
    have h2 : (2:ℂ)*c = 0 := by linear_combination hc
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hs := imaginaryVolume_square
  rw [h, hz, zero_smul, zero_mul] at hs
  exact one_ne_zero (neg_eq_zero.mp hs.symm)

theorem hermitianFamily_one_not_scalar (c : ℂ) :
    hermitianFamily 1 ≠ c • Kc := by
  intro h
  have hh := congrArg (fun A : CMatrix => Kc*A) h
  simp only [hermitianFamily, ← mul_assoc, Kc_square, one_mul, mul_smul_comm] at hh
  norm_num only [Complex.ofReal_one, one_smul] at hh
  have hw : W = (c-1) • (1 : CMatrix) := by
    have := eq_sub_of_add_eq' hh
    simpa only [sub_smul, one_smul] using this
  have he : imaginaryVolume = (c-1) • (1 : CCl) := by
    apply complexMatrixEquiv.injective
    simpa only [map_smul, map_one, W] using hw
  exact imaginaryVolume_not_complex_scalar (c-1) he

end HyperbolicSpinor
