import ControlsLean.Vision.Epipolar
import Mathlib

open Matrix

namespace ControlsLean.Vision.Explore

variable {K : Type*} [Field K]

theorem skew_mul_transpose (t : Fin 3 → K) :
    skew t * (skew t)ᵀ = (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) K) - vecMulVec t t := by
  rw [skew_transpose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [skew, Matrix.mul_apply, Fin.sum_univ_three, dotProduct, vecMulVec] <;> ring

theorem skew_mul_transpose_mul (t : Fin 3 → K) :
    skew t * (skew t)ᵀ * skew t = (t ⬝ᵥ t) • skew t := by
  rw [skew_transpose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [skew, Matrix.mul_apply, Fin.sum_univ_three, dotProduct] <;> ring

theorem trace_skew_mul_transpose (t : Fin 3 → K) :
    trace (skew t * (skew t)ᵀ) = 2 * (t ⬝ᵥ t) := by
  rw [skew_transpose]
  simp [skew, trace, Fin.sum_univ_three, dotProduct]; ring

theorem essential_mul_transpose {R : Matrix (Fin 3) (Fin 3) K} (hR : R * Rᵀ = 1)
    (t : Fin 3 → K) : essential R t * (essential R t)ᵀ = skew t * (skew t)ᵀ := by
  rw [essential, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc R, hR, Matrix.one_mul]

/-- **Demazure / Huang–Faugeras cubic** over any field (no `1/2`, so valid in char 2):
`2 E Eᵀ E = tr(E Eᵀ) E` whenever `R Rᵀ = 1`. -/
theorem cubic_constraint {R : Matrix (Fin 3) (Fin 3) K} (hR : R * Rᵀ = 1) (t : Fin 3 → K) :
    (2 : K) • (essential R t * (essential R t)ᵀ * essential R t) =
      trace (essential R t * (essential R t)ᵀ) • essential R t := by
  rw [essential_mul_transpose hR, trace_skew_mul_transpose, essential, ← Matrix.mul_assoc,
    skew_mul_transpose_mul, smul_mul_assoc, smul_smul]

/-- `E Eᵀ = ‖t‖² I - t tᵀ`: `E Eᵀ t = 0` and `E Eᵀ v = ‖t‖² v` for `v ⊥ t`, i.e. the
"singular values" are `‖t‖, ‖t‖, 0` (over ℝ). -/
theorem essential_mul_transpose_eq {R : Matrix (Fin 3) (Fin 3) K} (hR : R * Rᵀ = 1)
    (t : Fin 3 → K) :
    essential R t * (essential R t)ᵀ = (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) K) - vecMulVec t t := by
  rw [essential_mul_transpose hR, skew_mul_transpose]

/-! ### Scaling / sign of `t` -/

theorem skew_smul (c : K) (t : Fin 3 → K) : skew (c • t) = c • skew t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [skew]

theorem essential_smul (R : Matrix (Fin 3) (Fin 3) K) (c : K) (t : Fin 3 → K) :
    essential R (c • t) = c • essential R t := by
  rw [essential, essential, skew_smul, smul_mul_assoc]

theorem essential_neg (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K) :
    essential R (-t) = -essential R t := by
  have := essential_smul R (-1) t
  simpa using this

/-- **Cheirality is invisible to the epipolar constraint**: if `(d₁, d₂, R, t)` explains a
correspondence, so does `(-d₁, -d₂, R, -t)` — the scene point mirrored behind both cameras. -/
theorem mirror_reconstruction (R : Matrix (Fin 3) (Fin 3) K) (t x₁ x₂ : Fin 3 → K) (d₁ d₂ : K)
    (h : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) :
    (-d₂) • x₂ = R *ᵥ ((-d₁) • x₁) + (-t) := by
  rw [neg_smul, neg_smul, mulVec_neg, h, neg_add]

/-! ### The twisted pair -/

/-- Rotation by `π` about `t`: `2 t tᵀ / ‖t‖² - I`. -/
noncomputable def halfTurn (t : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  (2 / (t ⬝ᵥ t)) • vecMulVec t t - 1

theorem skew_mul_halfTurn {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) :
    skew t * halfTurn t = -skew t := by
  have h0 : skew t * vecMulVec t t = 0 := by
    rw [mul_vecMulVec, skew_mulVec, cross_self]; ext i j; simp [vecMulVec_apply]
  rw [halfTurn, Matrix.mul_sub, Matrix.mul_smul, h0, smul_zero, zero_sub, Matrix.mul_one]

theorem halfTurn_mul_transpose {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) :
    halfTurn t * (halfTurn t)ᵀ = 1 := by
  have hT : (halfTurn t)ᵀ = halfTurn t := by
    rw [halfTurn, transpose_sub, transpose_smul, transpose_vecMulVec, transpose_one]
  rw [hT, halfTurn, sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
    smul_mul_smul_comm, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul]
  have : 2 / (t ⬝ᵥ t) * (2 / (t ⬝ᵥ t)) * (t ⬝ᵥ t) = 2 * (2 / (t ⬝ᵥ t)) := by
    field_simp
  rw [this, mul_smul, two_smul]; abel

theorem det_halfTurn {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) : (halfTurn t).det = 1 := by
  have ht' : t 0 * t 0 + t 1 * t 1 + t 2 * t 2 ≠ 0 := by
    simpa [dotProduct, Fin.sum_univ_three] using ht
  simp only [halfTurn, det_fin_three, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    dotProduct, Fin.sum_univ_three, smul_eq_mul]
  simp only [one_apply_eq, ne_eq, Fin.reduceEq, not_false_eq_true, one_apply_ne]
  have hs : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 ≠ 0 := by simpa [sq] using ht'
  ring_nf
  field_simp
  ring

/-- **Twisted pair**: `(R, t)` and `(halfTurn t * R, -t)` give the *same* essential matrix,
and `halfTurn t * R` is again a rotation when `R` is. -/
theorem essential_twisted {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) (R : Matrix (Fin 3) (Fin 3) K) :
    essential (halfTurn t * R) (-t) = essential R t := by
  have hs : skew (-t) = -skew t := by simpa using skew_smul (-1 : K) t
  rw [essential, essential, hs, ← Matrix.mul_assoc, Matrix.neg_mul, skew_mul_halfTurn ht,
    Matrix.neg_mul, Matrix.neg_mul, neg_neg]

theorem twisted_orthogonal {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) {R : Matrix (Fin 3) (Fin 3) K}
    (hR : R * Rᵀ = 1) : (halfTurn t * R) * (halfTurn t * R)ᵀ = 1 := by
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc R, hR, Matrix.one_mul,
    halfTurn_mul_transpose ht]

theorem twisted_det {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) (R : Matrix (Fin 3) (Fin 3) K) :
    (halfTurn t * R).det = R.det := by
  rw [det_mul, det_halfTurn ht, one_mul]

/-- Hence (up to the overall sign of `E`) four poses `(R, ±t)`, `(halfTurn t R, ±t)`. The twisted
pair is a genuine second solution: `halfTurn t * R ≠ R` (in char ≠ 2, `t ≠ 0`). -/
theorem twisted_ne {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) (h2 : (2 : K) ≠ 0)
    {R : Matrix (Fin 3) (Fin 3) K} (hR : R * Rᵀ = 1) : halfTurn t * R ≠ R := by
  intro h
  have h1 : halfTurn t = 1 := by
    have := congrArg (· * Rᵀ) h
    simpa [Matrix.mul_assoc, hR] using this
  have := congrArg trace h1
  rw [halfTurn, trace_sub, trace_smul, trace_vecMulVec, trace_one, Fintype.card_fin,
    smul_eq_mul] at this
  field_simp at this
  norm_num at this
  have h3 : (2 : K) * 2 = 0 := by linear_combination -this
  exact h2 (by simpa using h3)

end ControlsLean.Vision.Explore
