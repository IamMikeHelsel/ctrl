/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Vision.Epipolar
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Algebraic constraints on the essential matrix

Let `E = [t]ₓ R` with `R` orthogonal (`Rᵀ R = 1`) over a field `K`, and write `s = t ⬝ᵥ t`
(over `ℝ` this is the squared Euclidean norm `‖t‖²`). We prove:

* `essential_mul_transpose`: `E Eᵀ = s I − t tᵀ`, and `trace_essential_mul_transpose`:
  `tr (E Eᵀ) = 2 s`.
* `essential_cubic_constraint` (**Demazure / Faugeras–Maybank**):
  `2 E Eᵀ E − tr (E Eᵀ) E = 0`.
* The singular-value structure: `E Eᵀ v = s v` for every `v ⊥ t`
  (`essential_mul_transpose_mulVec_of_orthogonal`) and `E Eᵀ t = 0`
  (`essential_mul_transpose_mulVec_self`): `E Eᵀ` acts as `s` on the plane `t^⊥` and kills
  `t`, i.e. (when `s ≠ 0`) the eigenvalues `s, s, 0` behind the singular values `‖t‖, ‖t‖, 0`.
  The eigenvector statements are what is proved; no spectrum/SVD theorem is stated.
* `transpose_essential_mulVec_self`: `Eᵀ t = 0`, the column form of `vecMul_essential`.
* The **twisted pair**: with `R_t(π) = (2 / s) t tᵀ − I` (rotation by `π` about `t`),
  `[t]ₓ (R_t(π) R) = −[t]ₓ R` for every `R` and `t` (`essential_twist`), so `R` and
  `R_t(π) R` give the same essential matrix up to sign. For `s ≠ 0`, `R_t(π)ᵀ R_t(π) = 1`,
  `det R_t(π) = 1` and `R_t(π) t = t`. Hence `R_t(π) ∈ SO(3, K)`, and over `ℝ` this holds for every
  `t ≠ 0` (`rotPiAbout_mem_specialOrthogonalGroup_real`); `R_t(π) R` is orthogonal with the
  same determinant as `R`.

The facts `det E = 0` and `tᵀ E = 0` are `det_essential` and `vecMul_essential` in
`ControlsLean.Vision.Epipolar` and are not repeated here.
-/

open Matrix

namespace ControlsLean.Vision

variable {K : Type*} [Field K]

/-- `[t]ₓ² = t tᵀ − (t ⬝ᵥ t) I`. -/
theorem skew_mul_skew (t : Fin 3 → K) :
    skew t * skew t = vecMulVec t t - (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew, mul_apply, vecMulVec_apply, dotProduct, Fin.sum_univ_three, one_apply] <;> ring

/-- `[t]ₓ t = 0`. -/
theorem skew_mulVec_self (t : Fin 3 → K) : skew t *ᵥ t = 0 := by
  rw [skew_mulVec, cross_self]

/-- `[t]ₓ t tᵀ = 0`. -/
theorem skew_mul_vecMulVec_self (t : Fin 3 → K) : skew t * vecMulVec t t = 0 := by
  ext i j
  have h := congrFun (skew_mulVec_self t) i
  simp only [mulVec, dotProduct, Pi.zero_apply] at h
  simp only [mul_apply, vecMulVec_apply, Matrix.zero_apply, ← mul_assoc, ← Finset.sum_mul, h,
    zero_mul]

/-- `t tᵀ [t]ₓ = 0`. -/
theorem vecMulVec_self_mul_skew (t : Fin 3 → K) : vecMulVec t t * skew t = 0 := by
  have h := congrArg transpose (skew_mul_vecMulVec_self t)
  rw [transpose_mul, transpose_vecMulVec, skew_transpose, transpose_zero, mul_neg,
    neg_eq_zero] at h
  exact h

/-- **`E Eᵀ = (t ⬝ᵥ t) I − t tᵀ`** for `E = [t]ₓ R` with `R` orthogonal. -/
theorem essential_mul_transpose {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1)
    (t : Fin 3 → K) :
    essential R t * (essential R t)ᵀ =
      (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) K) - vecMulVec t t := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  rw [essential, transpose_mul, skew_transpose, mul_assoc, ← mul_assoc R, hR', one_mul,
    mul_neg, skew_mul_skew, neg_sub]

/-- `tr (E Eᵀ) = 2 (t ⬝ᵥ t)`, i.e. `2 ‖t‖²` over `ℝ`. -/
theorem trace_essential_mul_transpose {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1)
    (t : Fin 3 → K) :
    trace (essential R t * (essential R t)ᵀ) = 2 * (t ⬝ᵥ t) := by
  rw [essential_mul_transpose hR]
  simp [trace_sub, trace_smul, trace_vecMulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- `E Eᵀ E = (t ⬝ᵥ t) E`. -/
theorem essential_mul_transpose_mul_essential {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1)
    (t : Fin 3 → K) :
    essential R t * (essential R t)ᵀ * essential R t = (t ⬝ᵥ t) • essential R t := by
  rw [essential_mul_transpose hR, essential, sub_mul, ← mul_assoc (vecMulVec t t),
    vecMulVec_self_mul_skew, zero_mul, sub_zero, smul_mul_assoc, one_mul]

/-- **Demazure / Faugeras–Maybank cubic constraint.** An essential matrix `E = [t]ₓ R` with
`R` orthogonal satisfies `2 E Eᵀ E − tr (E Eᵀ) E = 0`. -/
theorem essential_cubic_constraint {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1)
    (t : Fin 3 → K) :
    (2 : K) • (essential R t * (essential R t)ᵀ * essential R t) -
      trace (essential R t * (essential R t)ᵀ) • essential R t = 0 := by
  rw [essential_mul_transpose_mul_essential hR, trace_essential_mul_transpose hR, smul_smul,
    sub_self]

/-- `E Eᵀ v = (t ⬝ᵥ t) v` for every `v` orthogonal to `t`: the eigenvalue `‖t‖²` has the
two-dimensional eigenspace `t^⊥`. -/
theorem essential_mul_transpose_mulVec_of_orthogonal {R : Matrix (Fin 3) (Fin 3) K}
    (hR : Rᵀ * R = 1) (t v : Fin 3 → K) (hv : t ⬝ᵥ v = 0) :
    (essential R t * (essential R t)ᵀ) *ᵥ v = (t ⬝ᵥ t) • v := by
  rw [essential_mul_transpose hR, sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, hv,
    op_smul_eq_smul, zero_smul, sub_zero]

/-- `E Eᵀ t = 0`: the third eigenvalue of `E Eᵀ` is `0`, with eigenvector `t`. -/
theorem essential_mul_transpose_mulVec_self {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1)
    (t : Fin 3 → K) :
    (essential R t * (essential R t)ᵀ) *ᵥ t = 0 := by
  rw [essential_mul_transpose hR, sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, sub_self]

/-- `Eᵀ t = 0`: `t` is the left epipole (column form of `vecMul_essential`). -/
theorem transpose_essential_mulVec_self (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K) :
    (essential R t)ᵀ *ᵥ t = 0 := by
  rw [mulVec_transpose, vecMul_essential]

/-- The rotation by `π` about the axis `t`: `R_t(π) = (2 / (t ⬝ᵥ t)) t tᵀ − I`. -/
noncomputable def rotPiAbout (t : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  (2 / (t ⬝ᵥ t)) • vecMulVec t t - 1

theorem rotPiAbout_transpose (t : Fin 3 → K) : (rotPiAbout t)ᵀ = rotPiAbout t := by
  simp [rotPiAbout, transpose_sub, transpose_smul, transpose_vecMulVec]

/-- `R_t(π)` fixes its axis. -/
theorem rotPiAbout_mulVec_self {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) :
    rotPiAbout t *ᵥ t = t := by
  rw [rotPiAbout, sub_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul,
    one_mulVec,
    div_mul_cancel₀ _ ht, two_smul, add_sub_cancel_right]

/-- `R_t(π)` is orthogonal. -/
theorem rotPiAbout_transpose_mul_self {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) :
    (rotPiAbout t)ᵀ * rotPiAbout t = 1 := by
  have hsq : vecMulVec t t * vecMulVec t t = (t ⬝ᵥ t) • vecMulVec t t := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have hc :
      2 / (t ⬝ᵥ t) * (2 / (t ⬝ᵥ t)) * (t ⬝ᵥ t) = 2 / (t ⬝ᵥ t) + 2 / (t ⬝ᵥ t) := by
    field_simp
    ring
  rw [rotPiAbout_transpose, rotPiAbout, sub_mul, mul_sub, mul_sub, smul_mul_smul_comm, hsq,
    smul_smul, hc, add_smul, mul_one, one_mul, mul_one]
  abel

/-- Determinant of a scaled rank-one update of `−I`: `det (c t tᵀ − I) = c (t ⬝ᵥ t) − 1`. -/
theorem det_smul_vecMulVec_sub_one (c : K) (t : Fin 3 → K) :
    (c • vecMulVec t t - 1 : Matrix (Fin 3) (Fin 3) K).det = c * (t ⬝ᵥ t) - 1 := by
  simp [det_fin_three, vecMulVec_apply, dotProduct, Fin.sum_univ_three, one_apply]
  ring

/-- `det R_t(π) = 1`, so `R_t(π)` is a proper rotation. -/
theorem det_rotPiAbout {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) : (rotPiAbout t).det = 1 := by
  rw [rotPiAbout, det_smul_vecMulVec_sub_one, div_mul_cancel₀ _ ht]
  norm_num

/-- **Twisted pair.** Replacing `R` by `R_t(π) R` negates the essential matrix:
`[t]ₓ (R_t(π) R) = −[t]ₓ R`. Both therefore define the same essential matrix up to sign. -/
theorem essential_twist (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K) :
    essential (rotPiAbout t * R) t = -essential R t := by
  rw [essential, essential, ← mul_assoc, rotPiAbout, mul_sub, mul_smul_comm,
    skew_mul_vecMulVec_self, smul_zero, zero_sub, mul_one, neg_mul]

/-- The twisted rotation `R_t(π) R` is again orthogonal. -/
theorem rotPiAbout_mul_orthogonal {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1)
    {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) :
    (rotPiAbout t * R)ᵀ * (rotPiAbout t * R) = 1 := by
  rw [transpose_mul, mul_assoc, ← mul_assoc (rotPiAbout t)ᵀ, rotPiAbout_transpose_mul_self ht,
    one_mul, hR]

/-- The twisted rotation `R_t(π) R` has the same determinant as `R`. -/
theorem det_rotPiAbout_mul {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0)
    (R : Matrix (Fin 3) (Fin 3) K) :
    (rotPiAbout t * R).det = R.det := by
  rw [det_mul, det_rotPiAbout ht, one_mul]

/-- `R_t(π) ∈ SO(3, K)` whenever `t ⬝ᵥ t ≠ 0`. -/
theorem rotPiAbout_mem_specialOrthogonalGroup {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) :
    rotPiAbout t ∈ specialOrthogonalGroup (Fin 3) K :=
  ⟨(mem_orthogonalGroup_iff' (Fin 3) K).2 (rotPiAbout_transpose_mul_self ht), det_rotPiAbout ht⟩

/-- Over `ℝ`, `R_t(π) ∈ SO(3)` for every nonzero translation `t`. -/
theorem rotPiAbout_mem_specialOrthogonalGroup_real {t : Fin 3 → ℝ} (ht : t ≠ 0) :
    rotPiAbout t ∈ specialOrthogonalGroup (Fin 3) ℝ :=
  rotPiAbout_mem_specialOrthogonalGroup (mt dotProduct_self_eq_zero.1 ht)

end ControlsLean.Vision
