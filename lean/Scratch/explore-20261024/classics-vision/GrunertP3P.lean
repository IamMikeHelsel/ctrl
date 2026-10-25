import Mathlib

/-!
# Grunert 1841: perspective-three-point (P3P)

J. A. Grunert, "Das Pothenotische Problem in erweiterter Gestalt nebst über seine
Anwendungen in der Geodäsie", Grunerts Archiv für Mathematik und Physik 1 (1841), 238–248.
(Modern survey: Haralick, Lee, Ottenberg, Nölle, IJCV 13(3), 1994.)

Camera centre at the origin, unit bearing rays `uᵢ` (from calibrated pixels), unknown depths
`dᵢ`, camera-frame points `Pᵢ = dᵢ uᵢ`. Known world points `Wᵢ` with `R Wᵢ + t = Pᵢ`.

* `grunert_system`: true depths satisfy the three law-of-cosines equations
  `‖Wᵢ - Wⱼ‖² = dᵢ² + dⱼ² - 2 dᵢ dⱼ cos θᵢⱼ`, `cos θᵢⱼ = ⟪uᵢ, uⱼ⟫`.
* `pose_unique_of_depths`: the depths determine the pose: two proper rotations + translations
  mapping three non-collinear world points to the same camera-frame points are equal.
* `grunert_ratio_system`: Grunert's substitution `d₂ = v d₁`, `d₃ = w d₁`.
-/

open Matrix RealInnerProductSpace

namespace GrunertP3P

section LawOfCosines

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Law of cosines along two bearing rays. -/
theorem dist_sq_rays (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (a b : ℝ) :
    ‖a • u - b • v‖ ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * ⟪u, v⟫ := by
  rw [norm_sub_sq_real, norm_smul, norm_smul, hu, hv, inner_smul_left, inner_smul_right]
  simp only [Real.norm_eq_abs, mul_one, sq_abs, conj_trivial]; ring

/-- **Grunert's system.** If a rigid motion `g` (any isometry, affine or not) carries world
point `Wᵢ` to camera-frame point `dᵢ uᵢ`, the true depths satisfy the three law-of-cosines
equations with world-side distances and image-side cosines. -/
theorem grunert_system (g : E → E) (hg : Isometry g) (W u : Fin 3 → E) (hu : ∀ i, ‖u i‖ = 1)
    (d : Fin 3 → ℝ) (hW : ∀ i, g (W i) = d i • u i) (i j : Fin 3) :
    ‖W i - W j‖ ^ 2 = d i ^ 2 + d j ^ 2 - 2 * d i * d j * ⟪u i, u j⟫ := by
  rw [← dist_sq_rays _ _ (hu i) (hu j), ← hW, ← hW, ← dist_eq_norm, ← dist_eq_norm,
    hg.dist_eq]

/-- **Grunert's substitution** `d₂ = v d₁`, `d₃ = w d₁` (indices `0,1,2`): with
`a = ‖W₁ - W₂‖`, `b = ‖W₀ - W₂‖`, `c = ‖W₀ - W₁‖` and cosines `α, β, γ` opposite them. -/
theorem grunert_ratio_system (a b c α β γ d₁ v w : ℝ)
    (ha : a ^ 2 = (v * d₁) ^ 2 + (w * d₁) ^ 2 - 2 * (v * d₁) * (w * d₁) * α)
    (hb : b ^ 2 = d₁ ^ 2 + (w * d₁) ^ 2 - 2 * d₁ * (w * d₁) * β)
    (hc : c ^ 2 = d₁ ^ 2 + (v * d₁) ^ 2 - 2 * d₁ * (v * d₁) * γ) :
    a ^ 2 = d₁ ^ 2 * (v ^ 2 + w ^ 2 - 2 * v * w * α) ∧
    b ^ 2 = d₁ ^ 2 * (1 + w ^ 2 - 2 * w * β) ∧
    c ^ 2 = d₁ ^ 2 * (1 + v ^ 2 - 2 * v * γ) ∧
    -- eliminating `d₁²` gives Grunert's two conics in `(v, w)`
    a ^ 2 * (1 + v ^ 2 - 2 * v * γ) = c ^ 2 * (v ^ 2 + w ^ 2 - 2 * v * w * α) ∧
    b ^ 2 * (1 + v ^ 2 - 2 * v * γ) = c ^ 2 * (1 + w ^ 2 - 2 * w * β) := by
  refine ⟨by rw [ha]; ring, by rw [hb]; ring, by rw [hc]; ring, ?_, ?_⟩
  · rw [ha, hc]; ring
  · rw [hb, hc]; ring

end LawOfCosines

section Pose

/-- For any `3 × 3` matrix, `M a × M b = (adj M)ᵀ (a × b)`. -/
theorem mulVec_cross_mulVec {K : Type*} [CommRing K] (M : Matrix (Fin 3) (Fin 3) K)
    (a b : Fin 3 → K) :
    (M *ᵥ a) ⨯₃ (M *ᵥ b) = (adjugate M)ᵀ *ᵥ (a ⨯₃ b) := by
  ext i
  fin_cases i <;>
    simp [adjugate_fin_three, cross_apply, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- Proper rotations commute with the cross product. -/
theorem rot_cross {K : Type*} [CommRing K] (R : Matrix (Fin 3) (Fin 3) K)
    (hR : Rᵀ * R = 1) (hdet : R.det = 1) (a b : Fin 3 → K) :
    (R *ᵥ a) ⨯₃ (R *ᵥ b) = R *ᵥ (a ⨯₃ b) := by
  have hadj : adjugate R = Rᵀ := by
    have h1 : adjugate R * R = 1 := by rw [adjugate_mul, hdet, one_smul]
    have h2 : R * Rᵀ = 1 := mul_eq_one_comm.1 hR
    calc adjugate R = adjugate R * (R * Rᵀ) := by rw [h2, mul_one]
      _ = Rᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [mulVec_cross_mulVec, hadj, transpose_transpose]

/-- A linear map killing `a`, `b` and `a × b` with `a × b ≠ 0` is zero (over `ℝ`). -/
theorem eq_zero_of_kills_frame (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ)
    (hab : a ⨯₃ b ≠ 0) (ha : M *ᵥ a = 0) (hb : M *ᵥ b = 0) (hc : M *ᵥ (a ⨯₃ b) = 0) :
    M = 0 := by
  set B : Matrix (Fin 3) (Fin 3) ℝ := of ![a, b, a ⨯₃ b]
  have hdet : B.det ≠ 0 := by
    have : B.det = (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) := by
      rw [triple_product_permutation, triple_product_eq_det]
      rfl
    rw [this]
    intro h
    exact hab (dotProduct_self_eq_zero.1 h)
  have hMB : M * Bᵀ = 0 := by
    ext i j
    fin_cases j
    · simpa [B, mul_apply, mulVec, dotProduct] using congrFun ha i
    · simpa [B, mul_apply, mulVec, dotProduct] using congrFun hb i
    · simpa [B, mul_apply, mulVec, dotProduct] using congrFun hc i
  have hu : IsUnit Bᵀ.det := by rw [det_transpose]; exact Ne.isUnit hdet
  calc M = M * Bᵀ * Bᵀ⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = 0 := by rw [hMB, Matrix.zero_mul]

/-- **Depths determine the pose (P3P, final step).** If two proper rigid motions `(R, t)` and
`(R', t')` both send three non-collinear world points `Wᵢ` to the same camera-frame points
`Pᵢ = dᵢ uᵢ`, they coincide. Hence each real positive root of Grunert's system gives at most
one camera pose. -/
theorem pose_unique_of_depths (R R' : Matrix (Fin 3) (Fin 3) ℝ) (t t' : Fin 3 → ℝ)
    (hR : Rᵀ * R = 1) (hdet : R.det = 1) (hR' : R'ᵀ * R' = 1) (hdet' : R'.det = 1)
    (W P : Fin 3 → Fin 3 → ℝ) (hnc : (W 1 - W 0) ⨯₃ (W 2 - W 0) ≠ 0)
    (h : ∀ i, R *ᵥ W i + t = P i) (h' : ∀ i, R' *ᵥ W i + t' = P i) :
    R = R' ∧ t = t' := by
  set a := W 1 - W 0
  set b := W 2 - W 0
  have key : ∀ i j, R *ᵥ (W i - W j) = R' *ᵥ (W i - W j) := fun i j => by
    rw [mulVec_sub, mulVec_sub]
    have e1 := h i; have e2 := h j; have e3 := h' i; have e4 := h' j
    rw [← e3] at e1; rw [← e4] at e2
    have : R *ᵥ W i - R *ᵥ W j = (R *ᵥ W i + t) - (R *ᵥ W j + t) := by abel
    rw [this, e1, e2]; abel
  have hRR : R = R' := by
    rw [← sub_eq_zero]
    apply eq_zero_of_kills_frame _ a b hnc
    · rw [sub_mulVec, key, sub_self]
    · rw [sub_mulVec, key, sub_self]
    · rw [sub_mulVec, ← rot_cross R hR hdet, ← rot_cross R' hR' hdet', key 1 0, key 2 0,
        sub_self]
  refine ⟨hRR, ?_⟩
  have e := (h 0).trans (h' 0).symm
  rw [hRR] at e
  exact add_left_cancel e

/-- **P3P end-to-end uniqueness.** Given bearings and depths, a pose is determined. -/
theorem pose_unique_of_bearings_depths (R R' : Matrix (Fin 3) (Fin 3) ℝ) (t t' : Fin 3 → ℝ)
    (hR : Rᵀ * R = 1) (hdet : R.det = 1) (hR' : R'ᵀ * R' = 1) (hdet' : R'.det = 1)
    (W u : Fin 3 → Fin 3 → ℝ) (d : Fin 3 → ℝ) (hnc : (W 1 - W 0) ⨯₃ (W 2 - W 0) ≠ 0)
    (h : ∀ i, R *ᵥ W i + t = d i • u i) (h' : ∀ i, R' *ᵥ W i + t' = d i • u i) :
    R = R' ∧ t = t' :=
  pose_unique_of_depths R R' t t' hR hdet hR' hdet' W (fun i => d i • u i) hnc h h'

end Pose

end GrunertP3P
