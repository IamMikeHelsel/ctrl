import HyperbolicSpinor
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
namespace HyperbolicSpinor

abbrev W7 := Fin 7 → ℝ
abbrev S7 := Spinor ℝ W7

def spinBasis : Module.Basis (Finset (Fin 7)) ℝ S7 :=
  (Pi.basisFun ℝ (Fin 7)).ExteriorAlgebra

theorem spinor_finrank : Module.finrank ℝ S7 = 128 := by
  rw [Module.finrank_eq_card_basis spinBasis]
  norm_num

def matrixAction : CliffordAlgebra (QuadraticForm.dualProd ℝ W7) →ₐ[ℝ]
    Matrix (Finset (Fin 7)) (Finset (Fin 7)) ℝ :=
  (LinearMap.toMatrixAlgEquiv spinBasis).toAlgHom.comp (action ℝ W7)

/-- Actual endomorphism coordinates, without a claim of surjectivity. -/
theorem matrixAction_ι (p : Hyperbolic ℝ W7) :
    matrixAction (CliffordAlgebra.ι (QuadraticForm.dualProd ℝ W7) p) =
      LinearMap.toMatrix spinBasis spinBasis (cliffordVector ℝ W7 p) := by
  simp only [matrixAction, AlgHom.comp_apply, action_ι]
  rfl

end HyperbolicSpinor
