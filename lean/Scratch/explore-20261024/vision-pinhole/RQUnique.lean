import Mathlib

/-!
Scratch: uniqueness of the RQ decomposition `M = K R` (K upper triangular with positive
diagonal, R orthogonal), for any finite linearly ordered index type. This is the
uniqueness half of "recover intrinsics from `P = K [R | t]`".
-/

open Matrix

namespace RQScratch

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

omit [DecidableEq n] in
/-- Diagonal of a product of upper-triangular matrices is the product of diagonals. -/
theorem diag_mul_of_upper {A B : Matrix n n ℝ} (hA : A.IsUpperTriangular)
    (hB : B.IsUpperTriangular) (i : n) : (A * B) i i = A i i * B i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

/-- An orthogonal upper-triangular matrix with positive diagonal is the identity. -/
theorem eq_one_of_upper_orthogonal {U : Matrix n n ℝ} (hU : U.IsUpperTriangular)
    (hUU : U * Uᵀ = 1) (hpos : ∀ i, 0 < U i i) : U = 1 := by
  have : Invertible U := invertibleOfRightInverse U Uᵀ hUU
  have hinv : U⁻¹ = Uᵀ := inv_eq_right_inv hUU
  have hT : Uᵀ.IsUpperTriangular := hinv ▸ blockTriangular_inv_of_blockTriangular hU
  have hoff : ∀ i j, i ≠ j → U i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · simpa using hT h
    · exact hU h
  have hdiag : ∀ i, U i i = 1 := by
    intro i
    have h1 : (U * Uᵀ) i i = 1 := by rw [hUU]; simp
    rw [mul_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hoff i j (Ne.symm hj)])
      (by simp)] at h1
    simp only [transpose_apply] at h1
    nlinarith [hpos i]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [hdiag]
  · simp [hoff i j hij, hij]

/-- **RQ uniqueness.** If `K₁ Q₁ = K₂ Q₂` with `Kᵢ` upper triangular with positive
diagonal and `Qᵢ` orthogonal, then `K₁ = K₂` and `Q₁ = Q₂`. -/
theorem rq_unique {K₁ K₂ Q₁ Q₂ : Matrix n n ℝ}
    (hK₁ : K₁.IsUpperTriangular) (hK₂ : K₂.IsUpperTriangular)
    (hp₁ : ∀ i, 0 < K₁ i i) (hp₂ : ∀ i, 0 < K₂ i i)
    (hQ₁ : Q₁ * Q₁ᵀ = 1) (hQ₂ : Q₂ * Q₂ᵀ = 1) (h : K₁ * Q₁ = K₂ * Q₂) :
    K₁ = K₂ ∧ Q₁ = Q₂ := by
  have hdet : ∀ {A : Matrix n n ℝ}, A.IsUpperTriangular → (∀ i, 0 < A i i) →
      IsUnit A.det := fun hA hp => by
    rw [det_of_isUpperTriangular hA]
    exact (Finset.prod_pos fun i _ => hp i).ne'.isUnit
  have hd₁ := hdet hK₁ hp₁
  have hd₂ := hdet hK₂ hp₂
  have : Invertible K₂ := invertibleOfIsUnitDet K₂ hd₂
  have hK₂inv : K₂⁻¹.IsUpperTriangular := blockTriangular_inv_of_blockTriangular hK₂
  set U := K₂⁻¹ * K₁ with hUdef
  have hU : U.IsUpperTriangular := hK₂inv.mul hK₁
  have hQ₁' : Q₁ᵀ * Q₁ = 1 := mul_eq_one_comm.mp hQ₁
  have hUQ : U = Q₂ * Q₁ᵀ := by
    calc U = K₂⁻¹ * (K₁ * Q₁) * Q₁ᵀ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hQ₁, Matrix.mul_one]
      _ = Q₂ * Q₁ᵀ := by rw [h, ← Matrix.mul_assoc, nonsing_inv_mul K₂ hd₂, Matrix.one_mul]
  have hUU : U * Uᵀ = 1 := by
    rw [hUQ, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Q₁ᵀ,
      hQ₁', Matrix.one_mul, hQ₂]
  have hpos : ∀ i, 0 < U i i := by
    intro i
    have hinvdiag : K₂⁻¹ i i * K₂ i i = 1 := by
      rw [← diag_mul_of_upper hK₂inv hK₂, nonsing_inv_mul K₂ hd₂, one_apply_eq]
    have hpi : 0 < K₂⁻¹ i i := by
      by_contra hc
      push Not at hc
      nlinarith [hp₂ i]
    rw [hUdef, diag_mul_of_upper hK₂inv hK₁]
    exact mul_pos hpi (hp₁ i)
  have hU1 : U = 1 := eq_one_of_upper_orthogonal hU hUU hpos
  have hK : K₁ = K₂ := by
    have := congrArg (K₂ * ·) hU1
    simpa [hUdef, ← Matrix.mul_assoc, mul_nonsing_inv K₂ hd₂] using this
  refine ⟨hK, ?_⟩
  subst hK
  have := congrArg (K₁⁻¹ * ·) h
  simpa [← Matrix.mul_assoc, nonsing_inv_mul K₁ hd₁] using this

/-- Specialisation to camera matrices: the left 3×3 block `M = K R` of `P = K [R | t]`
determines `K` and `R` uniquely under the usual sign conventions. -/
theorem intrinsics_unique {K₁ K₂ R₁ R₂ : Matrix (Fin 3) (Fin 3) ℝ}
    (hK₁ : K₁.IsUpperTriangular) (hK₂ : K₂.IsUpperTriangular)
    (hp₁ : ∀ i, 0 < K₁ i i) (hp₂ : ∀ i, 0 < K₂ i i)
    (hR₁ : R₁ * R₁ᵀ = 1) (hR₂ : R₂ * R₂ᵀ = 1) (h : K₁ * R₁ = K₂ * R₂) :
    K₁ = K₂ ∧ R₁ = R₂ :=
  rq_unique hK₁ hK₂ hp₁ hp₂ hR₁ hR₂ h

/-- **Cholesky-type uniqueness / the IAC determines `K`.** If `K₁ K₁ᵀ = K₂ K₂ᵀ` with both
upper triangular with positive diagonal, then `K₁ = K₂`. -/
theorem upper_cholesky_unique {K₁ K₂ : Matrix n n ℝ}
    (hK₁ : K₁.IsUpperTriangular) (hK₂ : K₂.IsUpperTriangular)
    (hp₁ : ∀ i, 0 < K₁ i i) (hp₂ : ∀ i, 0 < K₂ i i) (h : K₁ * K₁ᵀ = K₂ * K₂ᵀ) :
    K₁ = K₂ := by
  have hd₂ : IsUnit K₂.det := by
    rw [det_of_isUpperTriangular hK₂]
    exact (Finset.prod_pos fun i _ => hp₂ i).ne'.isUnit
  set Q := K₂⁻¹ * K₁
  have hQ : Q * Qᵀ = 1 := by
    simp only [Q, transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc K₁, h, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      nonsing_inv_mul K₂ hd₂, Matrix.one_mul, ← transpose_mul, nonsing_inv_mul K₂ hd₂,
      transpose_one]
  have hKQ : K₁ * 1 = K₂ * Q := by
    simp [Q, ← Matrix.mul_assoc, mul_nonsing_inv K₂ hd₂]
  exact (rq_unique hK₁ hK₂ hp₁ hp₂ (by simp) hQ hKQ).1

/-- Positivity of the diagonal is necessary: flipping signs gives a second RQ factorisation. -/
theorem rq_not_unique_without_positivity :
    let D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, -1, 1]
    D.IsUpperTriangular ∧ D * Dᵀ = 1 ∧ (1 : Matrix (Fin 3) (Fin 3) ℝ) * 1 = D * D ∧ D ≠ 1 := by
  intro D
  refine ⟨Matrix.blockTriangular_diagonal _, ?_, ?_, ?_⟩
  · simp only [D, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  · simp only [D, Matrix.diagonal_mul_diagonal, Matrix.mul_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [D] at this
    norm_num at this

end RQScratch
