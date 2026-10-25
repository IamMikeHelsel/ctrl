import ControlsLean.Vision.HomographyUniqueness

open Matrix

namespace VisionExplore
open ControlsLean.Vision

variable {K : Type*} [Field K]

/-- Shorthand: the 3×3 bracket `[p q r]`. -/
abbrev br (p q r : Fin 3 → K) : K := (Matrix.of ![p, q, r]).det

/-- Cramer / Grassmann–Plücker identity: any four vectors in `K³` satisfy
`[p₀p₁p₂] p₃ = [p₃p₁p₂] p₀ + [p₀p₃p₂] p₁ + [p₀p₁p₃] p₂`. -/
theorem cramer4 (p₀ p₁ p₂ p₃ : Fin 3 → K) :
    br p₀ p₁ p₂ • p₃ = br p₃ p₁ p₂ • p₀ + br p₀ p₃ p₂ • p₁ + br p₀ p₁ p₃ • p₂ := by
  ext i
  simp only [br, det_fin_three]
  fin_cases i <;> simp <;> ring

/-- **General position ⇒ frame coefficients.** If `p₀,p₁,p₂` are independent, then
`p₃ = c₀p₀ + c₁p₁ + c₂p₂` with `cᵢ = [..p₃..]/[p₀p₁p₂]`, and each `cᵢ ≠ 0` iff the
corresponding triple containing `p₃` is non-collinear. -/
theorem frame_coeffs (p₀ p₁ p₂ p₃ : Fin 3 → K) (h : br p₀ p₁ p₂ ≠ 0) :
    p₃ = (br p₃ p₁ p₂ / br p₀ p₁ p₂) • p₀ + (br p₀ p₃ p₂ / br p₀ p₁ p₂) • p₁ +
      (br p₀ p₁ p₃ / br p₀ p₁ p₂) • p₂ := by
  have := congrArg ((br p₀ p₁ p₂)⁻¹ • ·) (cramer4 p₀ p₁ p₂ p₃)
  simp only [smul_add, smul_smul, inv_mul_cancel₀ h, one_smul] at this
  simp only [div_eq_inv_mul]; exact this

/-- **No-three-collinear ⇒ the hypothesis `hB` of `homography_rigidity_of_general_position`.**
With the Cramer coefficients, `frameBasisMatrix` is invertible exactly when all four
triples are non-collinear. -/
theorem frameBasis_det_ne_zero (p₀ p₁ p₂ p₃ : Fin 3 → K)
    (h012 : br p₀ p₁ p₂ ≠ 0) (h312 : br p₃ p₁ p₂ ≠ 0) (h032 : br p₀ p₃ p₂ ≠ 0)
    (h013 : br p₀ p₁ p₃ ≠ 0) :
    (frameBasisMatrix p₀ p₁ p₂ (br p₃ p₁ p₂ / br p₀ p₁ p₂) (br p₀ p₃ p₂ / br p₀ p₁ p₂)
      (br p₀ p₁ p₃ / br p₀ p₁ p₂)).det ≠ 0 := by
  rw [det_frameBasisMatrix]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (div_ne_zero h312 h012) (div_ne_zero h032 h012))
    (div_ne_zero h013 h012)) h012

/-- **Rigidity from the natural "no three collinear" hypothesis** (no `B_inv` needed). -/
theorem rigidity_no_three_collinear (H : Matrix (Fin 3) (Fin 3) K) (p₀ p₁ p₂ p₃ : Fin 3 → K)
    (h012 : br p₀ p₁ p₂ ≠ 0) (h312 : br p₃ p₁ p₂ ≠ 0) (h032 : br p₀ p₃ p₂ ≠ 0)
    (h013 : br p₀ p₁ p₃ ≠ 0) (s₀ s₁ s₂ s₃ : K)
    (h₀ : H *ᵥ p₀ = s₀ • p₀) (h₁ : H *ᵥ p₁ = s₁ • p₁) (h₂ : H *ᵥ p₂ = s₂ • p₂)
    (h₃ : H *ᵥ p₃ = s₃ • p₃) :
    H = s₃ • (1 : Matrix (Fin 3) (Fin 3) K) := by
  set B := frameBasisMatrix p₀ p₁ p₂ (br p₃ p₁ p₂ / br p₀ p₁ p₂) (br p₀ p₃ p₂ / br p₀ p₁ p₂)
      (br p₀ p₁ p₃ / br p₀ p₁ p₂)
  have hdet : IsUnit B.det := isUnit_iff_ne_zero.mpr (frameBasis_det_ne_zero _ _ _ _ h012 h312 h032 h013)
  exact (homography_rigidity_of_general_position H p₀ p₁ p₂ p₃ _ _ _
    (frame_coeffs p₀ p₁ p₂ p₃ h012) B⁻¹ (nonsing_inv_mul B hdet) s₀ s₁ s₂ s₃ h₀ h₁ h₂ h₃).2

/-- **Counterexample: 3 collinear points do not pin down the homography.**
The frame `e₀, e₁, e₂, e₀+e₁` has `e₀, e₁, e₀+e₁` collinear; `diag(1,1,2)` is invertible,
fixes all four rays, and is not a scalar matrix. -/
theorem collinear_counterexample :
    let p₃ : Fin 3 → ℚ := ![1, 1, 0]
    let H : Matrix (Fin 3) (Fin 3) ℚ := Matrix.diagonal ![1, 1, 2]
    H.det ≠ 0 ∧ br (e₀ : Fin 3 → ℚ) e₁ p₃ = 0 ∧
      H *ᵥ e₀ = (1 : ℚ) • e₀ ∧ H *ᵥ e₁ = (1 : ℚ) • e₁ ∧ H *ᵥ e₂ = (2 : ℚ) • e₂ ∧
      H *ᵥ p₃ = (1 : ℚ) • p₃ ∧ ∀ c : ℚ, H ≠ c • 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [det_diagonal, Fin.prod_univ_three]
  · simp [br, det_fin_three, e₀, e₁]
  · ext i; fin_cases i <;> simp [e₀, mulVec, dotProduct, diagonal]
  · ext i; fin_cases i <;> simp [e₁, mulVec, dotProduct, diagonal]
  · ext i; fin_cases i <;> simp [e₂, mulVec, dotProduct, diagonal]
  · ext i; fin_cases i <;> simp [mulVec, dotProduct, diagonal]
  · intro c hc
    have h0 := congrFun (congrFun hc 0) 0
    have h2 := congrFun (congrFun hc 2) 2
    simp [diagonal] at h0 h2
    rw [← h0] at h2; norm_num at h2

/-- **Existence (the half missing from `HomographyUniqueness`).** If `(p₀..p₃)` and `(q₀..q₃)`
are frames with invertible frame matrices `B`, `B'`, then `H := B' B⁻¹` maps each `pᵢ` to a
nonzero multiple of `qᵢ` and is invertible. -/
theorem exists_homography_of_frames (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : Fin 3 → K) (c₀ c₁ c₂ c₀' c₁' c₂' : K)
    (hp₃ : p₃ = c₀ • p₀ + c₁ • p₁ + c₂ • p₂) (hq₃ : q₃ = c₀' • q₀ + c₁' • q₁ + c₂' • q₂)
    (hB : (frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂).det ≠ 0)
    (hB' : (frameBasisMatrix q₀ q₁ q₂ c₀' c₁' c₂').det ≠ 0) :
    ∃ H : Matrix (Fin 3) (Fin 3) K, H.det ≠ 0 ∧
      c₀ • (H *ᵥ p₀) = c₀' • q₀ ∧ c₁ • (H *ᵥ p₁) = c₁' • q₁ ∧ c₂ • (H *ᵥ p₂) = c₂' • q₂ ∧
      H *ᵥ p₃ = q₃ := by
  set B := frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂
  set B' := frameBasisMatrix q₀ q₁ q₂ c₀' c₁' c₂'
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have key : ∀ v, (B' * B⁻¹) *ᵥ (B *ᵥ v) = B' *ᵥ v := fun v => by
    rw [mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul B hu, Matrix.mul_one]
  refine ⟨B' * B⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · simp [det_mul, hB, hB']
  · have := key e₀
    rwa [frameBasisMatrix_mulVec_e₀, frameBasisMatrix_mulVec_e₀, mulVec_smul] at this
  · have := key e₁
    rwa [frameBasisMatrix_mulVec_e₁, frameBasisMatrix_mulVec_e₁, mulVec_smul] at this
  · have := key e₂
    rwa [frameBasisMatrix_mulVec_e₂, frameBasisMatrix_mulVec_e₂, mulVec_smul] at this
  · have := key e₃
    rwa [frameBasisMatrix_mulVec_e₃ p₀ p₁ p₂ p₃ c₀ c₁ c₂ hp₃,
      frameBasisMatrix_mulVec_e₃ q₀ q₁ q₂ q₃ c₀' c₁' c₂' hq₃] at this

end VisionExplore
