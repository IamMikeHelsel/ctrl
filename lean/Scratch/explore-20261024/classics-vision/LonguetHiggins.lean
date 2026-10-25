import ControlsLean.Vision.Epipolar
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Longuet-Higgins 1981: conventions and translation recovery

H. C. Longuet-Higgins, "A computer algorithm for reconstructing a scene from two projections",
Nature 293 (1981), 133–135.

The paper writes the motion as `X' = R (X - T)` and `Q = R S` with `S = [T]ₓ`; the repo
(`ControlsLean/Vision/Epipolar.lean`) writes `X₂ = R X₁ + t` and `E = [t]ₓ R`.
* `skew_rot_mul`: `[R v]ₓ R = R [v]ₓ` for proper rotations, hence
* `essential_eq_neg_LH`: with `t = -R T`, the repo's `E` is `-(R [T]ₓ)` — same projective class.
* `essential_mul_transpose_eq`: `E Eᵀ = ‖t‖² I - t tᵀ` (the paper's route to `T`: `tr(E Eᵀ) =
  2‖t‖²` and the diagonal/off-diagonals of `E Eᵀ` give `t tᵀ`).
-/

open Matrix

namespace ControlsLean.Vision.LonguetHiggins

variable {K : Type*} [Field K]

theorem rot_cross (R : Matrix (Fin 3) (Fin 3) K) (hR : Rᵀ * R = 1) (hdet : R.det = 1)
    (a b : Fin 3 → K) : (R *ᵥ a) ⨯₃ (R *ᵥ b) = R *ᵥ (a ⨯₃ b) := by
  have hadj : adjugate R = Rᵀ := by
    have h1 : adjugate R * R = 1 := by rw [adjugate_mul, hdet, one_smul]
    calc adjugate R = adjugate R * (R * Rᵀ) := by rw [mul_eq_one_comm.1 hR, mul_one]
      _ = Rᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have : (R *ᵥ a) ⨯₃ (R *ᵥ b) = (adjugate R)ᵀ *ᵥ (a ⨯₃ b) := by
    ext i
    fin_cases i <;>
      simp [adjugate_fin_three, cross_apply, mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  rw [this, hadj, transpose_transpose]

theorem skew_rot_mul (R : Matrix (Fin 3) (Fin 3) K) (hR : Rᵀ * R = 1) (hdet : R.det = 1)
    (v : Fin 3 → K) : skew (R *ᵥ v) * R = R * skew v := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, skew_mulVec, skew_mulVec, rot_cross R hR hdet]

/-- Longuet-Higgins' `Q = R S` is, up to sign, the repo's essential matrix. -/
theorem essential_eq_neg_LH (R : Matrix (Fin 3) (Fin 3) K) (hR : Rᵀ * R = 1)
    (hdet : R.det = 1) (T : Fin 3 → K) :
    essential R (-(R *ᵥ T)) = -(R * skew T) := by
  have hneg : skew (-(R *ᵥ T)) = -skew (R *ᵥ T) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [skew]
  rw [essential, hneg, Matrix.neg_mul, skew_rot_mul R hR hdet]

theorem skew_mul_transpose (t : Fin 3 → K) :
    skew t * (skew t)ᵀ = (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) K) - vecMulVec t t := by
  rw [skew_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew, mul_apply, Fin.sum_univ_three, dotProduct, vecMulVec, one_apply] <;> ring

/-- **Translation recovery.** `E Eᵀ = (t·t) I - t tᵀ` for `E = [t]ₓ R`, `R Rᵀ = 1`. -/
theorem essential_mul_transpose_eq (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K)
    (hR : R * Rᵀ = 1) :
    essential R t * (essential R t)ᵀ =
      (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) K) - vecMulVec t t := by
  rw [essential, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc R, hR, Matrix.one_mul,
    skew_mul_transpose]

end ControlsLean.Vision.LonguetHiggins
