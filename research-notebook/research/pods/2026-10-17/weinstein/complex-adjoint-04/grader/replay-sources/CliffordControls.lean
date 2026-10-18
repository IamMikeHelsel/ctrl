import CliffordContraction

noncomputable section
open scoped BigOperators
namespace GUClifford
open GUContraction

def eta (i a:Ix) : ℝ := if a=i then 1 else 0
def delta (i j a b:Ix) : ℝ := eta i a * eta j b - eta j a * eta i b

def sectional : Tensor := fun a b c d => delta 0 1 a b * delta 0 1 c d

def fourform : Tensor := fun a b c d =>
  delta 0 1 a b * delta 2 3 c d - delta 0 2 a b * delta 1 3 c d +
  delta 0 3 a b * delta 1 2 c d + delta 2 3 a b * delta 0 1 c d -
  delta 1 3 a b * delta 0 2 c d + delta 1 2 a b * delta 0 3 c d

theorem sectional_curvature : Curvature sectional := by
  constructor
  · constructor <;> intros <;> unfold sectional delta <;> ring
  · intros; unfold sectional delta; ring

theorem sectional_component : sectional 0 1 0 1=1 := by norm_num [sectional,delta,eta]

theorem sectional_scalar : scal sectional=2 := by
  norm_num [scal,Ric,sectional,delta,eta,eps,mul_sub,sub_mul,mul_ite,ite_mul,
    Finset.sum_sub_distrib,Finset.sum_ite_irrel]

theorem sectional_K : K sectional=algebraMap ℝ Cl (-2) := by
  rw [actual_clifford_contraction sectional sectional_curvature, sectional_scalar]

theorem fourform_pair : PairSymmetries fourform := by
  constructor <;> intros <;> unfold fourform delta <;> ring

theorem fourform_middle_skew (a b c d:Ix) : fourform a b c d = -fourform a c b d := by
  unfold fourform delta
  ring

theorem fourform_support (a b c d:Ix)
    (h : a∉({0,1,2,3}:Finset Ix) ∨ b∉({0,1,2,3}:Finset Ix) ∨
      c∉({0,1,2,3}:Finset Ix) ∨ d∉({0,1,2,3}:Finset Ix)) : fourform a b c d=0 := by
  rcases h with h|h|h|h <;> simp_all [fourform,delta,eta]

theorem fourform_repeated (a b d:Ix) : fourform a b a d=0 := by
  unfold fourform delta
  ring

theorem fourform_Ric_zero (b d:Ix) : Ric fourform b d=0 := by
  simp [Ric,fourform_repeated]

theorem fourform_scalar_zero : scal fourform=0 := by simp [scal,fourform_Ric_zero]

theorem fourform_component : fourform 0 1 2 3=1 := by norm_num [fourform,delta,eta]

theorem fourform_bianchi_residual :
    fourform 0 1 2 3-fourform 0 2 1 3+fourform 0 3 1 2=3 := by
  norm_num [fourform,delta,eta]

theorem fourform_not_curvature : ¬Curvature fourform := by
  intro h
  have hb:=h.bianchi 0 1 2 3
  rw [fourform_bianchi_residual] at hb
  norm_num at hb

theorem gamma_move (a b:Ix) (h:a≠b) (x:Cl) :
    gamma a * (gamma b*x) = -(gamma b*(gamma a*x)) := by
  rw [← mul_assoc, gamma_swap a b h, neg_mul, mul_assoc]

theorem gamma_square_move (a:Ix) (x:Cl) : gamma a*(gamma a*x)=eps a • x := by
  rw [← mul_assoc,gamma_sq,smul_mul_assoc,one_mul]

def blade0123 : Cl := gamma 0*gamma 1*gamma 2*gamma 3

theorem blade0123_square : blade0123*blade0123=1 := by
  norm_num [blade0123,mul_assoc,
    gamma_move 3 2 (by decide),gamma_move 3 1 (by decide),gamma_move 3 0 (by decide),
    gamma_move 2 1 (by decide),gamma_move 2 0 (by decide),gamma_move 1 0 (by decide),
    gamma_square_move,gamma_sq,eps]

theorem blade0123_ne_zero : blade0123≠0 := by
  intro h
  have hs:=blade0123_square
  rw [h,zero_mul] at hs
  exact zero_ne_one hs

theorem fourform_total : total (rho fourform) gamma=(24:ℝ) • blade0123 := by
  simp only [total,rho,fourform,delta,eta,mul_sub,mul_add,
    sub_smul,add_smul,mul_ite,ite_smul,mul_zero,mul_one,
    zero_smul,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  norm_num [blade0123,mul_assoc,
    gamma_move 3 2 (by decide),gamma_move 3 1 (by decide),gamma_move 3 0 (by decide),
    gamma_move 2 1 (by decide),gamma_move 2 0 (by decide),gamma_move 1 0 (by decide),
    gamma_swap 3 2 (by decide),gamma_swap 3 1 (by decide),gamma_swap 3 0 (by decide),
    gamma_swap 2 1 (by decide),gamma_swap 2 0 (by decide),gamma_swap 1 0 (by decide),eps]
  module

theorem fourform_K : K fourform=(12:ℝ) • blade0123 := by
  have h:=actual_normalization_bridge fourform fourform_pair
  rw [fourform_total] at h
  calc
    K fourform=(1/2:ℝ) • ((2:ℝ) • K fourform) := by module
    _=(1/2:ℝ) • ((24:ℝ) • blade0123) := congrArg _ h.symm
    _=_ := by module

theorem fourform_K_ne_zero : K fourform≠0 := by
  rw [fourform_K]
  exact smul_ne_zero (by norm_num) blade0123_ne_zero

theorem dropping_bianchi_false : K fourform≠algebraMap ℝ Cl (-scal fourform) := by
  simpa [fourform_scalar_zero] using fourform_K_ne_zero

theorem no_universal_without_bianchi :
    ¬(∀ R:Tensor, PairSymmetries R → K R=algebraMap ℝ Cl (-scal R)) := by
  intro h
  exact dropping_bianchi_false (h fourform fourform_pair)

theorem sectional_false_positive_sign : K sectional≠algebraMap ℝ Cl (scal sectional) := by
  rw [sectional_K,sectional_scalar]
  intro h
  have hi : Function.Injective (algebraMap ℝ Cl) := (algebraMap ℝ Cl).injective
  have hh:=hi h
  norm_num at hh

end GUClifford
