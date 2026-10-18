import CliffordModel
import SpinorDimensions
import Mathlib.LinearAlgebra.Matrix.Dual

noncomputable section
namespace HyperbolicSpinor
open GUClifford

def low : V →ₗ[ℝ] W7 where
  toFun v j := v (Fin.castAdd 7 j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def high : V →ₗ[ℝ] W7 where
  toFun v j := v (Fin.natAdd 7 j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def splitLinear : V →ₗ[ℝ] Hyperbolic ℝ W7 :=
  LinearMap.prod ((dotProductEquiv ℝ (Fin 7)).toLinearMap.comp (low - high)) (low + high)

theorem splitLinear_form (v : V) :
    QuadraticForm.dualProd ℝ W7 (splitLinear v) = Q v := by
  rw [Q_apply]
  simp [splitLinear, low, high, dotProductEquiv, dotProduct, Fin.sum_univ_succ, eps]
  ring

def splitIsometry : Q →qᵢ QuadraticForm.dualProd ℝ W7 where
  toLinearMap := splitLinear
  map_app' := splitLinear_form

/-- The accepted Cl(7,7) now acts on a concrete 128-dimensional spinor space. -/
def splitAction : Cl →ₐ[ℝ] Module.End ℝ S7 :=
  (action ℝ W7).comp (CliffordAlgebra.map splitIsometry)

def splitMatrix : Cl →ₐ[ℝ] Matrix (Finset (Fin 7)) (Finset (Fin 7)) ℝ :=
  (LinearMap.toMatrixAlgEquiv spinBasis).toAlgHom.comp splitAction

theorem splitAction_gamma (j : Ix) :
    splitAction (gamma j) = cliffordVector ℝ W7 (splitLinear (e j)) := by
  simp only [splitAction, AlgHom.comp_apply, gamma, CliffordAlgebra.map_apply_ι, action_ι]
  rfl

theorem splitMatrix_one : splitMatrix 1 = 1 := map_one splitMatrix

theorem splitMatrix_mul (a b : Cl) : splitMatrix (a*b) = splitMatrix a * splitMatrix b :=
  map_mul splitMatrix a b

/-- This is a representation. Its injectivity is a separate, still open gate. -/
theorem splitMatrix_relation (a b : Ix) :
    splitMatrix (gamma a) * splitMatrix (gamma b) +
    splitMatrix (gamma b) * splitMatrix (gamma a) =
      (if a=b then 2 * eps a else 0) • (1 : Matrix (Finset (Fin 7)) (Finset (Fin 7)) ℝ) := by
  rw [← map_mul, ← map_mul, ← map_add, gamma_relation]
  split_ifs <;> simp

theorem splitMatrix_gamma_sq (a : Ix) :
    splitMatrix (gamma a) * splitMatrix (gamma a) =
      eps a • (1 : Matrix (Finset (Fin 7)) (Finset (Fin 7)) ℝ) := by
  rw [← map_mul, gamma_sq]
  simp

theorem positive_square : splitMatrix (gamma 0) * splitMatrix (gamma 0) = 1 := by
  simpa [eps] using splitMatrix_gamma_sq 0

theorem negative_square : splitMatrix (gamma 7) * splitMatrix (gamma 7) = -1 := by
  simpa [eps] using splitMatrix_gamma_sq 7

theorem positive_not_zero : splitMatrix (gamma 0) ≠ 0 := by
  intro h
  have hs := positive_square
  rw [h, zero_mul] at hs
  exact zero_ne_one hs

theorem negative_square_not_positive :
    splitMatrix (gamma 7) * splitMatrix (gamma 7) ≠ 1 := by
  rw [negative_square]
  intro h
  have hd := congrFun (congrFun h ∅) ∅
  norm_num at hd

theorem clifford_finrank : Module.finrank ℝ Cl = 16384 := by
  rw [(CliffordAlgebra.equivExterior Q).finrank_eq]
  rw [Module.finrank_eq_card_basis ((Pi.basisFun ℝ Ix).ExteriorAlgebra)]
  norm_num [Ix]

end HyperbolicSpinor
