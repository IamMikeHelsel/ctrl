import ComplexAdjoint

noncomputable section
open scoped TensorProduct
namespace GUComplex
open GUClifford

def realStar : Cl →ₗ[ℝ] Cl where
  toFun := star
  map_add' := star_add
  map_smul' := CliffordAlgebra.star_smul

-- This is the actual complex-linear extension of the scalar-fixed real star.
def fixedBar : CCl →ₗ[ℝ] CCl := TensorProduct.map (LinearMap.id) realStar

theorem fixedBar_tmul (z : ℂ) (a : Cl) : fixedBar (z ⊗ₜ[ℝ] a) = z ⊗ₜ[ℝ] star a := rfl

theorem fixedBar_smul (z : ℂ) (a : CCl) : fixedBar (z • a) = z • fixedBar a := by
  induction a using TensorProduct.inductionOn with
  | tmul w a => simp [TensorProduct.smul_tmul', fixedBar_tmul]
  | add a b ha hb => simp [smul_add, ha, hb]

theorem fixedBar_involutive (a : CCl) : fixedBar (fixedBar a) = a := by
  induction a using TensorProduct.inductionOn with
  | tmul z a => simp only [fixedBar_tmul, star_star]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem fixedBar_mul (a b : CCl) : fixedBar (a*b) = fixedBar b * fixedBar a := by
  induction a using TensorProduct.inductionOn with
  | tmul z a =>
    induction b using TensorProduct.inductionOn with
    | tmul w b =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, fixedBar_tmul, star_mul]
      rw [mul_comm z w]
    | add b c hb hc => simp only [mul_add, map_add, hb, hc, add_mul]
  | add a b ha hb => simp only [add_mul, map_add, ha, hb, mul_add]

theorem fixedBar_scalar (z : ℂ) : fixedBar (algebraMap ℂ CCl z) = algebraMap ℂ CCl z := by
  simp [Algebra.TensorProduct.algebraMap_apply, fixedBar_tmul]

theorem fixedBar_gamma (a : Ix) : fixedBar (cgamma a) = -cgamma a := by
  change (1 : ℂ) ⊗ₜ[ℝ] star (gamma a) = -((1 : ℂ) ⊗ₜ[ℝ] gamma a)
  rw [gamma, CliffordAlgebra.star_ι, TensorProduct.tmul_neg]

theorem iAnti_gamma_zero : iAnti (cgamma 0) (cgamma 0) = algebraMap ℂ CCl (2*Complex.I) := by
  unfold iAnti
  rw [cgamma_zero_sq]
  rw [Algebra.smul_def Complex.I (1+1 : CCl)]
  simp only [map_mul, map_ofNat]
  noncomm_ring

theorem iAnti_gamma_zero_ne_zero : iAnti (cgamma 0) (cgamma 0) ≠ 0 := by
  rw [iAnti_gamma_zero]
  exact (map_ne_zero (algebraMap ℂ CCl)).mpr (by simp)

theorem fixedBar_iAnti_fixed :
    fixedBar (iAnti (cgamma 0) (cgamma 0)) = iAnti (cgamma 0) (cgamma 0) := by
  rw [iAnti_gamma_zero, fixedBar_scalar]

theorem fixedBar_iAnti_not_skew :
    fixedBar (iAnti (cgamma 0) (cgamma 0)) ≠ -iAnti (cgamma 0) (cgamma 0) := by
  rw [fixedBar_iAnti_fixed, iAnti_gamma_zero]
  intro h
  have hs : (2*Complex.I : ℂ) = -(2*Complex.I) := by
    apply scalar_injective
    rw [map_neg]
    exact h
  have hi := congrArg Complex.im hs
  norm_num at hi

theorem fixedBar_closure_false :
    ¬ (∀ a b : CCl, fixedBar a = -a → fixedBar b = -b →
      fixedBar (iAnti a b) = -iAnti a b) := by
  intro h
  exact fixedBar_iAnti_not_skew (h _ _ (fixedBar_gamma 0) (fixedBar_gamma 0))

theorem bar_I_scalar_ne_same :
    bar (algebraMap ℂ CCl Complex.I) ≠ algebraMap ℂ CCl Complex.I := by
  rw [bar_scalar]
  intro h
  have hi := congrArg Complex.im (scalar_injective h)
  norm_num at hi

theorem anticommutator_without_I_not_skew :
    ¬ Skew (cgamma 0 * cgamma 0 + cgamma 0 * cgamma 0) := by
  rw [cgamma_zero_sq]
  intro h
  change bar ((1 : CCl)+1) = -(1+1) at h
  have hs : (1 : CCl)+1 = -((1 : CCl)+1) := by
    simpa only [bar, star_add, star_one] using h
  have hc : (1+1 : ℂ) = -(1+1 : ℂ) := by
    apply scalar_injective
    simpa only [map_neg, map_add, map_one] using hs
  norm_num at hc

theorem cgamma_swap (a b : Ix) (h : a ≠ b) : cgamma a * cgamma b = -(cgamma b * cgamma a) := by
  simpa only [cgamma, map_mul, map_neg] using congrArg embed (gamma_swap a b h)

theorem mixed_blade_square :
    (cgamma 0 * cgamma 7) * (cgamma 0 * cgamma 7) = 1 := by
  calc
    _ = cgamma 0 * (cgamma 7 * cgamma 0) * cgamma 7 := by noncomm_ring
    _ = cgamma 0 * (-(cgamma 0 * cgamma 7)) * cgamma 7 := by
      rw [cgamma_swap 7 0 (by decide)]
    _ = -(cgamma 0 * cgamma 0) * (cgamma 7 * cgamma 7) := by
      rw [mul_neg (cgamma 0) (cgamma 0 * cgamma 7),
        neg_mul (cgamma 0 * (cgamma 0 * cgamma 7)) (cgamma 7),
        neg_mul (cgamma 0 * cgamma 0) (cgamma 7 * cgamma 7)]
      simp only [mul_assoc]
    _ = 1 := by
      rw [cgamma_zero_sq, cgamma_seven_sq, neg_mul_neg (1 : CCl) 1, one_mul]

theorem bar_product_wrong_order_false :
    bar (cgamma 0 * cgamma 7) ≠ bar (cgamma 0) * bar (cgamma 7) := by
  intro h
  rw [bar_mul, bar_gamma, bar_gamma,
    neg_mul_neg (cgamma 7) (cgamma 0), neg_mul_neg (cgamma 0) (cgamma 7),
    cgamma_swap 7 0 (by decide)] at h
  have hm := congrArg (fun x : CCl => x * (cgamma 0 * cgamma 7)) h
  rw [neg_mul (cgamma 0 * cgamma 7) (cgamma 0 * cgamma 7), mixed_blade_square] at hm
  have hc : (-1 : ℂ) = 1 := by
    apply scalar_injective
    simpa only [map_neg, map_one] using hm
  norm_num at hc

end GUComplex
