import HermitianFamily
noncomputable section
namespace M09Actual
open HyperbolicSpinor GUClifford GUComplex

def G : CMatrix := complexMatrixEquiv (cgamma 7)

theorem G_square : G*G= -1 := by
  rw [G,← map_mul,cgamma_seven_sq,map_neg,map_one]

theorem G_form_skew : G.conjTranspose*Kc= -(Kc*G) := by
  have hb : Kc*G.conjTranspose*Kc= -G := by
    rw [G,← complexMatrixEquiv_bar,bar_gamma,map_neg]
  have hh := congrArg (fun X : CMatrix => Kc*X) hb
  simpa only [← mul_assoc,Kc_square,one_mul,mul_neg] using hh

theorem G_K_unitary : G.conjTranspose*Kc*G=Kc := by
  rw [G_form_skew,neg_mul,mul_assoc,G_square,mul_neg,mul_one,neg_neg]

theorem G_W_anti : G*W= -(W*G) := by
  have ha : imaginaryVolume*cgamma 7= -(cgamma 7*imaginaryVolume) := by
    dsimp [imaginaryVolume,complexVolume,cgamma]
    rw [smul_mul_assoc,mul_smul_comm,← map_mul,← map_mul,
      chirality_anticommutes_gamma,map_neg,smul_neg]
  have hb := congrArg complexMatrixEquiv ha
  have hc : W*G= -(G*W) := by simpa only [map_mul,map_neg,W,G] using hb
  have hd := congrArg (fun X : CMatrix => -X) hc
  simpa only [neg_neg] using hd.symm

theorem actual_form_sign_flip (t : ℝ) :
    G.conjTranspose*hermitianFamily t*G=hermitianFamily (-t) := by
  have hi : G*W*G=W := by
    rw [G_W_anti,neg_mul,mul_assoc,G_square,mul_neg,mul_one,neg_neg]
  have hw : G.conjTranspose*Kc*W*G= -(Kc*W) := by
    rw [G_form_skew,neg_mul,neg_mul,mul_assoc,mul_assoc,← mul_assoc G W G,hi]
  simp only [hermitianFamily,Complex.ofReal_neg,mul_add,mul_one,add_mul,
    mul_smul_comm,smul_mul_assoc,← mul_assoc]
  rw [G_K_unitary,hw,smul_neg,neg_smul]
theorem fixed_generator_adjoint_residual (t : ℝ) :
    hermitianFamily t*G+G.conjTranspose*hermitianFamily t =
      (2*(t:ℂ)) • (Kc*W*G) := by
  have hd : G.conjTranspose*Kc*W=Kc*W*G := by
    rw [G_form_skew,neg_mul,mul_assoc,G_W_anti,mul_neg,neg_neg,mul_assoc]
  simp only [hermitianFamily,mul_add,mul_one,add_mul,mul_smul_comm,
    smul_mul_assoc,← mul_assoc]
  rw [hd,G_form_skew]
  module

theorem fixed_generator_skew_only_zero (t : ℝ)
    (h : hermitianFamily t*G+G.conjTranspose*hermitianFamily t=0) : t=0 := by
  have hp : (Kc*W*G)*(G*W*Kc)=1 := by
    calc
      _ = Kc*(W*(G*G)*W)*Kc := by noncomm_ring
      _ = Kc*(-(W*W))*Kc := by rw [G_square]; noncomm_ring
      _ = 1 := by rw [W_square,neg_neg,mul_one,Kc_square]
  have hn : Kc*W*G ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at hp
    exact zero_ne_one hp
  rw [fixed_generator_adjoint_residual] at h
  have hc : (2*(t:ℂ))=0 := (smul_eq_zero.mp h).resolve_right hn
  have ht : (t:ℂ)=0 := (mul_eq_zero.mp hc).resolve_left (by norm_num)
  exact_mod_cast ht
end M09Actual
#print axioms M09Actual.G_square
#print axioms M09Actual.G_form_skew
#print axioms M09Actual.G_K_unitary
#print axioms M09Actual.G_W_anti
#print axioms M09Actual.actual_form_sign_flip

#print axioms M09Actual.fixed_generator_adjoint_residual
#print axioms M09Actual.fixed_generator_skew_only_zero
