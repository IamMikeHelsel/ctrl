import RealAdjoint
import ComplexAdjoint
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Maps

noncomputable section
open scoped TensorProduct
namespace HyperbolicSpinor
open GUClifford GUComplex

abbrev CMatrix := Matrix (Finset J) (Finset J) ℂ

/-- Entrywise scalar extension; matrix multiplication is retained. -/
def realToComplexMatrix : SpinMatrix →ₐ[ℝ] CMatrix :=
  (Algebra.ofId ℝ ℂ).mapMatrix

@[simp] theorem realToComplexMatrix_apply (A : SpinMatrix) (I J : Finset J) :
    realToComplexMatrix A I J = (A I J : ℂ) := rfl

/-- The two finite product maps supply an explicit linear inverse. -/
def complexLinearEquiv : CCl ≃ₗ[ℂ] CMatrix :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : ℂ ≃ₐ[ℂ] ℂ) splitMatrixEquiv).toLinearEquiv ≪≫ₗ
  TensorProduct.piRight ℝ ℂ ℂ (fun _ : Finset J => Finset J → ℝ) ≪≫ₗ
  LinearEquiv.piCongrRight (fun _ : Finset J => TensorProduct.piScalarRight ℝ ℂ ℂ (Finset J))

@[simp] theorem complexLinearEquiv_tmul (z : ℂ) (a : Cl) :
    complexLinearEquiv (z ⊗ₜ[ℝ] a) = z • realToComplexMatrix (splitMatrixEquiv a) := by
  ext I T
  change (splitMatrixEquiv a I T : ℂ) * z = z * (splitMatrixEquiv a I T : ℂ)
  exact mul_comm _ _

/-- This uses genuine matrix multiplication, not pointwise function multiplication. -/
def complexMatrixEquiv : CCl ≃ₐ[ℂ] CMatrix :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct complexLinearEquiv
    (by
      intro z w a b
      simp only [complexLinearEquiv_tmul, map_mul]
      exact (smul_mul_smul_comm z _ w _).symm)
    (by simp)

@[simp] theorem complexMatrixEquiv_tmul (z : ℂ) (a : Cl) :
    complexMatrixEquiv (z ⊗ₜ[ℝ] a) = z • realToComplexMatrix (splitMatrixEquiv a) :=
  complexLinearEquiv_tmul z a

@[simp] theorem complexMatrixEquiv_tmul_entry (z : ℂ) (a : Cl) (I T : Finset J) :
    complexMatrixEquiv (z ⊗ₜ[ℝ] a) I T = z * (splitMatrixEquiv a I T : ℂ) := by
  rw [complexMatrixEquiv_tmul]
  rfl

theorem complexMatrixEquiv_bijective : Function.Bijective complexMatrixEquiv :=
  complexMatrixEquiv.bijective

end HyperbolicSpinor
