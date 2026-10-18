import FullImage
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace HyperbolicSpinor
open GUClifford

/-- Faithfulness uses the proved full image as well as the dimension equality. -/
theorem splitMatrix_injective : Function.Injective splitMatrix := by
  let : FiniteDimensional ℝ Cl := Module.finite_of_finrank_pos (by rw [clifford_finrank]; norm_num)
  have hd : Module.finrank ℝ Cl =
      Module.finrank ℝ (Matrix (Finset (Fin 7)) (Finset (Fin 7)) ℝ) := by
    rw [clifford_finrank, Module.finrank_matrix]
    norm_num
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd
    (f := splitMatrix.toLinearMap)).mpr splitMatrix_surjective

/-- The concrete real split Clifford algebra is the full 128 by 128 real matrix algebra. -/
def splitMatrixEquiv : Cl ≃ₐ[ℝ] Matrix (Finset (Fin 7)) (Finset (Fin 7)) ℝ :=
  AlgEquiv.ofBijective splitMatrix ⟨splitMatrix_injective, splitMatrix_surjective⟩

@[simp] theorem splitMatrixEquiv_apply (x : Cl) : splitMatrixEquiv x = splitMatrix x := rfl

theorem splitAction_injective : Function.Injective splitAction := by
  intro x y h
  apply splitMatrix_injective
  change LinearMap.toMatrixAlgEquiv spinBasis (splitAction x) =
    LinearMap.toMatrixAlgEquiv spinBasis (splitAction y)
  rw [h]

end HyperbolicSpinor
