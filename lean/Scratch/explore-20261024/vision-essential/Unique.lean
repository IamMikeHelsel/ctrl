import ControlsLean.Vision.Epipolar
import Mathlib

/-!
Uniqueness of the essential-matrix decomposition: `[t]ₓ R = [t']ₓ R'` with `R, R'` orthogonal of
the *same determinant* forces `(R', t') = (R, t)` or the twisted pair `(halfTurn t * R, -t)`.
Without the determinant condition there are extra (reflection) solutions: see `reflection_pair`.
-/

open Matrix

namespace ControlsLean.Vision.Explore

variable {K : Type*} [Field K]

noncomputable def halfTurn (t : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  (2 / (t ⬝ᵥ t)) • vecMulVec t t - 1

/-- Householder reflection in the plane `⊥ t`. -/
noncomputable def householder (t : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  1 - (2 / (t ⬝ᵥ t)) • vecMulVec t t

theorem skew_mul_vecMulVec_self (t u : Fin 3 → K) : skew t * vecMulVec t u = 0 := by
  rw [mul_vecMulVec, skew_mulVec, cross_self]; ext i j; simp [vecMulVec_apply]

theorem skew_mul_halfTurn (t : Fin 3 → K) : skew t * halfTurn t = -skew t := by
  rw [halfTurn, Matrix.mul_sub, Matrix.mul_smul, skew_mul_vecMulVec_self, smul_zero, zero_sub,
    Matrix.mul_one]

theorem skew_mul_householder (t : Fin 3 → K) : skew t * householder t = skew t := by
  rw [householder, Matrix.mul_sub, Matrix.mul_smul, skew_mul_vecMulVec_self, smul_zero, sub_zero,
    Matrix.mul_one]

theorem halfTurn_sq {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) : halfTurn t * halfTurn t = 1 := by
  rw [halfTurn, sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
    smul_mul_smul_comm, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul]
  have : 2 / (t ⬝ᵥ t) * (2 / (t ⬝ᵥ t)) * (t ⬝ᵥ t) = 2 * (2 / (t ⬝ᵥ t)) := by field_simp
  rw [this, mul_smul, two_smul]; abel

theorem householder_mul_transpose {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) :
    householder t * (householder t)ᵀ = 1 := by
  rw [householder, transpose_sub, transpose_smul, transpose_vecMulVec, transpose_one, sub_mul,
    mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    smul_mul_smul_comm, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul]
  have : 2 / (t ⬝ᵥ t) * (2 / (t ⬝ᵥ t)) * (t ⬝ᵥ t) = 2 * (2 / (t ⬝ᵥ t)) := by field_simp
  rw [this, mul_smul, two_smul]; abel

theorem det_householder {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) : (householder t).det = -1 := by
  have ht' : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 ≠ 0 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using ht
  simp only [householder, det_fin_three, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    dotProduct, Fin.sum_univ_three, smul_eq_mul]
  simp only [one_apply_eq, ne_eq, Fin.reduceEq, not_false_eq_true, one_apply_ne]
  ring_nf
  field_simp
  ring

/-- **Reflection ambiguity**: if only `R Rᵀ = 1` is assumed (as in `ControlsLean.Vision.essential`,
which allows any `R`), `(householder t * R, t)` is a further decomposition of the same `E`, with
`det` of the opposite sign. So over `O(3)` there are 8 (not 4) sign-normalised decompositions. -/
theorem reflection_pair (t : Fin 3 → K) (R : Matrix (Fin 3) (Fin 3) K) :
    essential (householder t * R) t = essential R t := by
  rw [essential, essential, ← Matrix.mul_assoc, skew_mul_householder]

/-- `[t]ₓ² = t tᵀ - ‖t‖² I`. -/
theorem skew_mul_skew (t : Fin 3 → K) :
    skew t * skew t = vecMulVec t t - (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [skew, Matrix.mul_apply, Fin.sum_univ_three, dotProduct, vecMulVec] <;> ring

/-- Kernel of `M ↦ [t]ₓ M`: such `M` are `t uᵀ`. -/
theorem eq_vecMulVec_of_skew_mul {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) {M : Matrix (Fin 3) (Fin 3) K}
    (h : skew t * M = 0) : M = vecMulVec t ((t ⬝ᵥ t)⁻¹ • (t ᵥ* M)) := by
  have h2 : skew t * skew t * M = 0 := by rw [Matrix.mul_assoc, h, Matrix.mul_zero]
  rw [skew_mul_skew, sub_mul, smul_mul_assoc, Matrix.one_mul, sub_eq_zero, vecMulVec_mul] at h2
  rw [vecMulVec_smul, h2, smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem det_one_add_vecMulVec (t u : Fin 3 → K) :
    (1 + vecMulVec t u).det = 1 + u ⬝ᵥ t := by
  simp [det_fin_three, vecMulVec_apply, dotProduct, Fin.sum_univ_three, one_apply]; ring

/-- Key rigidity: an orthogonal `D` with `det D = 1` fixing `[t]ₓ` from the right is `1`. -/
theorem eq_one_of_skew_mul {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) {D : Matrix (Fin 3) (Fin 3) K}
    (hD : D * Dᵀ = 1) (hdet : D.det = 1) (h : skew t * D = skew t) : D = 1 := by
  set u := (t ⬝ᵥ t)⁻¹ • (t ᵥ* (D - 1))
  have hM := eq_vecMulVec_of_skew_mul ht (M := D - 1) (by rw [Matrix.mul_sub, h, Matrix.mul_one,
    sub_self])
  have hDu : D = 1 + vecMulVec t u := by rw [← hM]; abel
  have hut : u ⬝ᵥ t = 0 := by
    have := det_one_add_vecMulVec t u
    rw [← hDu, hdet] at this; linear_combination -this
  have hDD : Dᵀ * D = 1 := mul_eq_one_comm.mp hD
  rw [hDu, transpose_add, transpose_one, transpose_vecMulVec, add_mul, mul_add, mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, vecMulVec_mul_vecMulVec] at hDD
  have hv := congrArg (· *ᵥ t) hDD
  simp only [add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hut,
    dotProduct_comm t u] at hv
  have hu0 : (t ⬝ᵥ t) • u = 0 := by
    simpa [smul_dotProduct, hut, op_smul_eq_smul] using hv
  have : u = 0 := by
    rw [← one_smul K u, ← inv_mul_cancel₀ ht, mul_smul, hu0, smul_zero]
  rw [hDu, this]; ext i j; simp [vecMulVec_apply]

theorem eq_or_eq_neg_of_vecMulVec {t t' : Fin 3 → K} (h : vecMulVec t t = vecMulVec t' t') :
    t' = t ∨ t' = -t := by
  have hij : ∀ i j, t i * t j = t' i * t' j := fun i j => by
    simpa [vecMulVec_apply] using congrFun (congrFun h i) j
  by_cases ht : t = 0
  · left
    subst ht
    funext i
    have := hij i i
    simp only [Pi.zero_apply, zero_mul] at this ⊢
    exact mul_self_eq_zero.mp this.symm
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 := by
    by_contra hc; push Not at hc; exact ht (funext hc)
  have hii := hij i i
  have hsq : (t' i - t i) * (t' i + t i) = 0 := by linear_combination -hii
  rcases mul_eq_zero.mp hsq with h1 | h1
  · left; funext j
    have hj := hij i j
    have : t' i = t i := sub_eq_zero.mp h1
    rw [this] at hj
    exact (mul_left_cancel₀ hi hj).symm
  · right; funext j
    have hj := hij i j
    have : t' i = -t i := eq_neg_of_add_eq_zero_left h1
    rw [this] at hj
    have : t i * t j = t i * (-t' j) := by rw [hj]; ring
    have := mul_left_cancel₀ hi this
    simp only [Pi.neg_apply]
    linear_combination this

theorem det_halfTurn {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) : (halfTurn t).det = 1 := by
  have ht' : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 ≠ 0 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using ht
  simp only [halfTurn, det_fin_three, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    dotProduct, Fin.sum_univ_three, smul_eq_mul]
  simp only [one_apply_eq, ne_eq, Fin.reduceEq, not_false_eq_true, one_apply_ne]
  ring_nf
  field_simp
  ring

theorem halfTurn_transpose (t : Fin 3 → K) : (halfTurn t)ᵀ = halfTurn t := by
  rw [halfTurn, transpose_sub, transpose_smul, transpose_vecMulVec, transpose_one]

theorem skew_mul_transpose' (t : Fin 3 → K) :
    skew t * (skew t)ᵀ = (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) K) - vecMulVec t t := by
  rw [skew_transpose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [skew, Matrix.mul_apply, Fin.sum_univ_three, dotProduct, vecMulVec] <;> ring

/-- Same translation ⇒ same rotation (given equal determinants). -/
theorem eq_of_skew_mul_eq {t : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0) {R R' : Matrix (Fin 3) (Fin 3) K}
    (hR : R * Rᵀ = 1) (hR' : R' * R'ᵀ = 1) (hdet : R'.det = R.det)
    (h : skew t * R = skew t * R') : R' = R := by
  have hRR : Rᵀ * R = 1 := mul_eq_one_comm.mp hR
  have hD : skew t * (R' * Rᵀ) = skew t := by
    rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc, hR, Matrix.mul_one]
  have hDD : (R' * Rᵀ) * (R' * Rᵀ)ᵀ = 1 := by
    rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hRR,
      Matrix.one_mul, hR']
  have hdetD : (R' * Rᵀ).det = 1 := by
    have := congrArg det hR
    rw [det_mul, det_transpose, det_one] at this
    rw [det_mul, det_transpose, hdet, this]
  have h1 := eq_one_of_skew_mul ht hDD hdetD hD
  calc R' = R' * Rᵀ * R := by rw [Matrix.mul_assoc, hRR, Matrix.mul_one]
    _ = R := by rw [h1, Matrix.one_mul]

/-- **Exactly two decompositions** of a nonzero essential matrix with fixed `‖t‖`-normalisation
up to the twisted pair: if `[t]ₓ R = [t']ₓ R'` with `R, R'` orthogonal of equal determinant,
then `(R', t') = (R, t)` or `(R', t') = (halfTurn t * R, -t)`. Together with `E ↦ -E`
(`t ↦ -t`) this gives the classical four solutions. -/
theorem decomposition_unique (h2 : (2 : K) ≠ 0) {t t' : Fin 3 → K} (ht : t ⬝ᵥ t ≠ 0)
    {R R' : Matrix (Fin 3) (Fin 3) K} (hR : R * Rᵀ = 1) (hR' : R' * R'ᵀ = 1)
    (hdet : R'.det = R.det) (h : essential R t = essential R' t') :
    (t' = t ∧ R' = R) ∨ (t' = -t ∧ R' = halfTurn t * R) := by
  have hEE : skew t * (skew t)ᵀ = skew t' * (skew t')ᵀ := by
    have := congrArg (fun E => E * Eᵀ) h
    simp only [essential, transpose_mul, Matrix.mul_assoc] at this
    rwa [← Matrix.mul_assoc R, hR, ← Matrix.mul_assoc R', hR', Matrix.one_mul,
      Matrix.one_mul] at this
  rw [skew_mul_transpose', skew_mul_transpose'] at hEE
  have hs : t ⬝ᵥ t = t' ⬝ᵥ t' := by
    have := congrArg trace hEE
    simp only [trace_sub, trace_smul, trace_one, Fintype.card_fin, trace_vecMulVec,
      smul_eq_mul] at this
    have : (2 : K) * (t ⬝ᵥ t - t' ⬝ᵥ t') = 0 := by push_cast at this; linear_combination this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
  rw [hs] at hEE
  have hv : vecMulVec t t = vecMulVec t' t' := by
    have := congrArg (fun M => (t' ⬝ᵥ t') • (1 : Matrix (Fin 3) (Fin 3) K) - M) hEE
    simpa using this
  rcases eq_or_eq_neg_of_vecMulVec hv with rfl | rfl
  · exact Or.inl ⟨rfl, eq_of_skew_mul_eq ht hR hR' hdet h⟩
  · right
    refine ⟨rfl, ?_⟩
    have hneg : skew (-t) = -skew t := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [skew]
    have hR'' : (halfTurn t * R') * (halfTurn t * R')ᵀ = 1 := by
      rw [transpose_mul, halfTurn_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc R', hR',
        Matrix.one_mul, halfTurn_sq ht]
    have hdet'' : (halfTurn t * R').det = R.det := by rw [det_mul, det_halfTurn ht, one_mul, hdet]
    have hE : skew t * R = skew t * (halfTurn t * R') := by
      rw [← Matrix.mul_assoc, skew_mul_halfTurn]
      simpa [essential, hneg] using h
    have := eq_of_skew_mul_eq ht hR hR'' hdet'' hE
    rw [← this, ← Matrix.mul_assoc, halfTurn_sq ht, Matrix.one_mul]

end ControlsLean.Vision.Explore
