import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace V06
open Matrix

def rotation (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c,-s;s,c]
def frobSq (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ∑ i, ∑ j, (A i j)^2
/-- Gauge R0=I; observed rotations M01=M12=I, M02=-I; all weights one. -/
def objective (c₁ s₁ c₂ s₂ : ℝ) : ℝ :=
    frobSq (rotation c₁ s₁ - 1) + frobSq (rotation c₂ s₂ - rotation c₁ s₁) +
    frobSq (rotation c₂ s₂ + 1)

theorem rotation_det (c s : ℝ) (h : c^2+s^2=1) : (rotation c s).det=1 := by
  rw [Matrix.det_fin_two]
  simpa [rotation,pow_two] using h

theorem rotation_orthogonal (c s : ℝ) (h : c^2+s^2=1) :
    (rotation c s).transpose * rotation c s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotation, Matrix.mul_apply, Fin.sum_univ_two, pow_two] at * <;> nlinarith

theorem objective_expansion (c₁ s₁ c₂ s₂ : ℝ) :
    objective c₁ s₁ c₂ s₂ =
    2*((c₁-1)^2+s₁^2+(c₂-c₁)^2+(s₂-s₁)^2+(c₂+1)^2+s₂^2) := by
  simp [objective,frobSq,rotation,Fin.sum_univ_two]
  ring

theorem dual_slack_psd (x y z : ℝ) :
    0 ≤ x^2+y^2+z^2-2*x*y+2*x*z-2*y*z := by
  nlinarith [sq_nonneg (x-y+z)]

/-- Certificate equality on the actual gauge-fixed matrix objective. -/
theorem certificate_identity (c₁ s₁ c₂ s₂ : ℝ)
    (h₁ : c₁^2+s₁^2=1) (h₂ : c₂^2+s₂^2=1) :
    objective c₁ s₁ c₂ s₂ = 6+2*((1-c₁+c₂)^2+(s₂-s₁)^2) := by
  rw [objective_expansion]
  nlinarith

theorem global_lower_bound (c₁ s₁ c₂ s₂ : ℝ)
    (h₁ : c₁^2+s₁^2=1) (h₂ : c₂^2+s₂^2=1) :
    6 ≤ objective c₁ s₁ c₂ s₂ := by
  rw [certificate_identity _ _ _ _ h₁ h₂]
  nlinarith [sq_nonneg (1-c₁+c₂), sq_nonneg (s₂-s₁)]

theorem algebraic_candidate :
    (1/2 : ℝ)^2+(Real.sqrt 3/2)^2=1 ∧
    (-1/2 : ℝ)^2+(Real.sqrt 3/2)^2=1 ∧
    objective (1/2) (Real.sqrt 3/2) (-1/2) (Real.sqrt 3/2)=6 := by
  have hs : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have h₁ : (1/2 : ℝ)^2+(Real.sqrt 3/2)^2=1 := by nlinarith
  have h₂ : (-1/2 : ℝ)^2+(Real.sqrt 3/2)^2=1 := by nlinarith
  refine ⟨h₁,h₂,?_⟩
  rw [certificate_identity _ _ _ _ h₁ h₂]
  norm_num

theorem conjugate_candidate :
    objective (1/2) (-Real.sqrt 3/2) (-1/2) (-Real.sqrt 3/2)=6 := by
  have hs : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  rw [certificate_identity]
  · norm_num
  · nlinarith
  · nlinarith

theorem gauge_fixed_candidates_distinct :
    rotation (1/2) (Real.sqrt 3/2) ≠ rotation (1/2) (-Real.sqrt 3/2) := by
  intro h
  have he := congrFun (congrFun h 1) 0
  have hp : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.2 (by norm_num)
  norm_num [rotation] at he
  linarith

theorem identity_candidate_not_global : objective 1 0 1 0=8 ∧ 6<(8:ℝ) := by
  norm_num [objective_expansion]

/-- The scalar rotation parameterization covers every proper orthogonal2x2
matrix, rather than being an extra restriction of the graph problem. -/
theorem proper_rotation_parameterization (A : Matrix (Fin 2) (Fin 2) ℝ)
    (ho : A.transpose*A=1) (hd : A.det=1) :
    A=rotation (A 0 0) (A 1 0) ∧ (A 0 0)^2+(A 1 0)^2=1 := by
  have h0 := congrFun (congrFun ho 0) 0
  have h1 := congrFun (congrFun ho 1) 1
  norm_num [Matrix.mul_apply,Fin.sum_univ_two] at h0 h1
  rw [Matrix.det_fin_two] at hd
  have he : (A 0 1+A 1 0)^2+(A 1 1-A 0 0)^2=0 := by nlinarith
  have hb : A 0 1 = -A 1 0 := by
    nlinarith [sq_nonneg (A 0 1+A 1 0),sq_nonneg (A 1 1-A 0 0)]
  have hd' : A 1 1 = A 0 0 := by
    nlinarith [sq_nonneg (A 0 1+A 1 0),sq_nonneg (A 1 1-A 0 0)]
  refine ⟨?_,by nlinarith⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation,hb,hd']

/-- Actual matrix-objective global bound for all proper rotations after R0=I. -/
theorem global_matrix_bound (R₁ R₂ : Matrix (Fin 2) (Fin 2) ℝ)
    (h₁ : R₁.transpose*R₁=1) (d₁ : R₁.det=1)
    (h₂ : R₂.transpose*R₂=1) (d₂ : R₂.det=1) :
    6 ≤ frobSq (R₁-1)+frobSq (R₂-R₁)+frobSq (R₂+1) := by
  obtain ⟨e₁,n₁⟩ := proper_rotation_parameterization R₁ h₁ d₁
  obtain ⟨e₂,n₂⟩ := proper_rotation_parameterization R₂ h₂ d₂
  have h := global_lower_bound _ _ _ _ n₁ n₂
  change 6 ≤ frobSq (rotation (R₁ 0 0) (R₁ 1 0)-1)+
    frobSq (rotation (R₂ 0 0) (R₂ 1 0)-rotation (R₁ 0 0) (R₁ 1 0))+
    frobSq (rotation (R₂ 0 0) (R₂ 1 0)+1) at h
  simpa only [←e₁,←e₂] using h

#print axioms rotation_det
#print axioms rotation_orthogonal
#print axioms objective_expansion
#print axioms dual_slack_psd
#print axioms certificate_identity
#print axioms global_lower_bound
#print axioms algebraic_candidate
#print axioms conjugate_candidate
#print axioms gauge_fixed_candidates_distinct
#print axioms identity_candidate_not_global
#print axioms proper_rotation_parameterization
#print axioms global_matrix_bound
end V06
