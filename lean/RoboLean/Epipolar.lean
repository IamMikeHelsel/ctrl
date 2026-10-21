import Mathlib

/-!
# Two-view epipolar geometry for calibrated cameras

We work with points `Fin 3 → ℝ` and matrices `Matrix (Fin 3) (Fin 3) ℝ`. A calibrated two-view
configuration is a rigid motion `X ↦ R *ᵥ X + t` taking coordinates of a 3D point in camera 1 to
coordinates in camera 2.

## Main results

* `skew t` (the hat map `[t]×`) with `skew_mulVec : skew t *ᵥ v = t ⨯₃ v`.
* `mulVec_cross_of_mem_SO3`: rotations preserve cross products;
  `conj_skew_of_mem_SO3 : R * skew t * Rᵀ = skew (R *ᵥ t)`.
* `essential R t = skew t * R` and the epipolar constraint (`epipolar_constraint`,
  `epipolar_constraint_image`).
* `det_essential`, `left_epipole`, `right_epipole`.
* `huang_faugeras`: the cubic constraint `E Eᵀ E = ½ tr(E Eᵀ) E`, plus the spectral facts
  `essential_mul_transpose_mulVec_t` / `essential_mul_transpose_mulVec_orth` (the eigenvalues of
  `E Eᵀ` are `‖t‖², ‖t‖², 0`, i.e. `E` has two equal singular values and one zero).
* `planar_homography`: points on a plane `n ⬝ᵥ X = d` are mapped by `R + (1/d) t nᵀ`.
* `triangulation_unique`: depths are unique when the two rays are not parallel.
-/

open Matrix

namespace RoboLean.Epipolar

/-- The hat map `t ↦ [t]×`: the skew-symmetric matrix representing `v ↦ t ⨯₃ v`. -/
def skew (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -t 2, t 1; t 2, 0, -t 0; -t 1, t 0, 0]

/-- `[t]× v = t × v`. -/
theorem skew_mulVec (t v : Fin 3 → ℝ) : skew t *ᵥ v = t ⨯₃ v := by
  ext i; fin_cases i <;> simp [skew, crossProduct, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- `[t]×` is skew-symmetric. -/
theorem skew_transpose (t : Fin 3 → ℝ) : (skew t)ᵀ = -skew t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [skew]

/-- `[t]× t = 0`. -/
theorem skew_mulVec_self (t : Fin 3 → ℝ) : skew t *ᵥ t = 0 := by
  rw [skew_mulVec, cross_self]

/-- For any `3 × 3` matrix, `(M a) × (M b) = adj(M)ᵀ (a × b)` (cofactor identity). -/
theorem cross_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    (M *ᵥ a) ⨯₃ (M *ᵥ b) = (adjugate M)ᵀ *ᵥ (a ⨯₃ b) := by
  ext i; fin_cases i <;>
    simp [crossProduct, mulVec, dotProduct, Fin.sum_univ_three, adjugate_fin_three] <;> ring

/-- `det [t]× = 0`. -/
theorem det_skew (t : Fin 3 → ℝ) : (skew t).det = 0 := by
  simp [skew, det_fin_three]; ring

/-- `[t]× [t]×ᵀ [t]× = ‖t‖² [t]×`. -/
theorem skew_mul_transpose_mul (t : Fin 3 → ℝ) :
    skew t * (skew t)ᵀ * skew t = (t ⬝ᵥ t) • skew t := by
  rw [skew_transpose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [skew, Matrix.mul_apply, Fin.sum_univ_three, dotProduct] <;> ring

/-- `tr([t]× [t]×ᵀ) = 2 ‖t‖²`. -/
theorem trace_skew_mul_transpose (t : Fin 3 → ℝ) :
    trace (skew t * (skew t)ᵀ) = 2 * (t ⬝ᵥ t) := by
  rw [skew_transpose]
  simp [skew, trace, Fin.sum_univ_three, dotProduct]; ring


/-! ### Rotations -/

/-- For `R ∈ SO(3)`, `adj R = Rᵀ`. -/
theorem adjugate_of_mem_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) : adjugate R = Rᵀ := by
  obtain ⟨hO, hdet⟩ := mem_specialOrthogonalGroup_iff.mp hR
  have h1 : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hO
  calc adjugate R = Rᵀ * R * adjugate R := by rw [h1, Matrix.one_mul]
    _ = Rᵀ := by rw [Matrix.mul_assoc, mul_adjugate, hdet, one_smul, Matrix.mul_one]

/-- Rotations preserve cross products: `R (a × b) = (R a) × (R b)`. -/
theorem mulVec_cross_of_mem_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    R *ᵥ (a ⨯₃ b) = (R *ᵥ a) ⨯₃ (R *ᵥ b) := by
  rw [cross_mulVec, adjugate_of_mem_SO3 hR, transpose_transpose]

/-- Conjugating the hat map by a rotation: `R [t]× Rᵀ = [R t]×`. -/
theorem conj_skew_of_mem_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) (t : Fin 3 → ℝ) :
    R * skew t * Rᵀ = skew (R *ᵥ t) := by
  have h1 : R * Rᵀ = 1 := (mem_orthogonalGroup_iff (Fin 3) ℝ).mp (mem_specialOrthogonalGroup_iff.mp hR).1
  rw [ext_iff_mulVec]
  intro v
  rw [← mulVec_mulVec, ← mulVec_mulVec, skew_mulVec, skew_mulVec, mulVec_cross_of_mem_SO3 hR,
    mulVec_mulVec, h1, one_mulVec]

/-! ### Essential matrix -/

/-- The essential matrix `E = [t]× R` of the relative pose `X₂ = R X₁ + t`. -/
def essential (R : Matrix (Fin 3) (Fin 3) ℝ) (t : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  skew t * R

/-- `E v = t × (R v)`. -/
theorem essential_mulVec (R : Matrix (Fin 3) (Fin 3) ℝ) (t v : Fin 3 → ℝ) :
    essential R t *ᵥ v = t ⨯₃ (R *ᵥ v) := by
  rw [essential, ← mulVec_mulVec, skew_mulVec]

/-- **Epipolar constraint** (3D form): if `X₂ = R X₁ + t` then `X₂ᵀ E X₁ = 0`. -/
theorem epipolar_constraint (R : Matrix (Fin 3) (Fin 3) ℝ) (t X1 X2 : Fin 3 → ℝ)
    (h : X2 = R *ᵥ X1 + t) : X2 ⬝ᵥ (essential R t *ᵥ X1) = 0 := by
  rw [essential_mulVec, h, add_dotProduct, dot_cross_self, dot_self_cross, add_zero]

/-- **Epipolar constraint** (image form): if the image points `x₁, x₂` are seen at nonzero
depths `a, b`, i.e. `b x₂ = R (a x₁) + t`, then `x₂ᵀ E x₁ = 0`. -/
theorem epipolar_constraint_image (R : Matrix (Fin 3) (Fin 3) ℝ) (t x1 x2 : Fin 3 → ℝ)
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : b • x2 = R *ᵥ (a • x1) + t) :
    x2 ⬝ᵥ (essential R t *ᵥ x1) = 0 := by
  have := epipolar_constraint R t _ _ h
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hb
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' ha
    · exact h''

/-- Essential matrices are singular. -/
theorem det_essential (R : Matrix (Fin 3) (Fin 3) ℝ) (t : Fin 3 → ℝ) :
    (essential R t).det = 0 := by
  rw [essential, det_mul, det_skew, zero_mul]

/-- `tᵀ [t]× = 0`. -/
theorem vecMul_skew_self (t : Fin 3 → ℝ) : t ᵥ* skew t = 0 := by
  ext i; fin_cases i <;> simp [skew, vecMul, dotProduct, Fin.sum_univ_three] <;> ring

/-- The left epipole: `tᵀ E = 0`. -/
theorem left_epipole (R : Matrix (Fin 3) (Fin 3) ℝ) (t : Fin 3 → ℝ) :
    t ᵥ* essential R t = 0 := by
  rw [essential, ← vecMul_vecMul, vecMul_skew_self, zero_vecMul]

/-- The right epipole: `E (Rᵀ t) = 0` for orthogonal `R`. -/
theorem right_epipole {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ orthogonalGroup (Fin 3) ℝ)
    (t : Fin 3 → ℝ) : essential R t *ᵥ (Rᵀ *ᵥ t) = 0 := by
  rw [essential_mulVec, mulVec_mulVec, (mem_orthogonalGroup_iff (Fin 3) ℝ).mp hR, one_mulVec, cross_self]

/-- For orthogonal `R`, `E Eᵀ = [t]× [t]×ᵀ`. -/
theorem essential_mul_transpose {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ orthogonalGroup (Fin 3) ℝ) (t : Fin 3 → ℝ) :
    essential R t * (essential R t)ᵀ = skew t * (skew t)ᵀ := by
  rw [essential, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc R,
    (mem_orthogonalGroup_iff (Fin 3) ℝ).mp hR, Matrix.one_mul]

/-- `[t]× [t]×ᵀ = ‖t‖² I − t tᵀ`. -/
theorem skew_mul_transpose (t : Fin 3 → ℝ) :
    skew t * (skew t)ᵀ = (t ⬝ᵥ t) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec t t := by
  rw [skew_transpose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [skew, Matrix.mul_apply, Fin.sum_univ_three, dotProduct, vecMulVec] <;> ring

/-- `tr(E Eᵀ) = 2 ‖t‖²`. -/
theorem trace_essential_mul_transpose {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ orthogonalGroup (Fin 3) ℝ) (t : Fin 3 → ℝ) :
    trace (essential R t * (essential R t)ᵀ) = 2 * (t ⬝ᵥ t) := by
  rw [essential_mul_transpose hR, trace_skew_mul_transpose]

/-- **Huang–Faugeras cubic constraint**: `E Eᵀ E = ½ tr(E Eᵀ) E` for `E = [t]× R`,
`R` orthogonal. -/
theorem huang_faugeras {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ orthogonalGroup (Fin 3) ℝ) (t : Fin 3 → ℝ) :
    essential R t * (essential R t)ᵀ * essential R t =
      ((1 / 2 : ℝ) * trace (essential R t * (essential R t)ᵀ)) • essential R t := by
  rw [trace_essential_mul_transpose hR, essential_mul_transpose hR, essential,
    ← Matrix.mul_assoc, skew_mul_transpose_mul, smul_mul_assoc]
  congr 1; ring

/-- `t` is in the kernel of `E Eᵀ` (eigenvalue `0`). -/
theorem essential_mul_transpose_mulVec_t {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ orthogonalGroup (Fin 3) ℝ) (t : Fin 3 → ℝ) :
    (essential R t * (essential R t)ᵀ) *ᵥ t = 0 := by
  rw [essential_mul_transpose hR, skew_transpose, Matrix.mul_neg, neg_mulVec, ← mulVec_mulVec,
    skew_mulVec_self, mulVec_zero, neg_zero]

/-- Every `v ⊥ t` is an eigenvector of `E Eᵀ` with eigenvalue `‖t‖²`; together with
`essential_mul_transpose_mulVec_t` this says the singular values of `E` are `‖t‖, ‖t‖, 0`. -/
theorem essential_mul_transpose_mulVec_orth {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ orthogonalGroup (Fin 3) ℝ) {t v : Fin 3 → ℝ} (hv : t ⬝ᵥ v = 0) :
    (essential R t * (essential R t)ᵀ) *ᵥ v = (t ⬝ᵥ t) • v := by
  rw [essential_mul_transpose hR, skew_mul_transpose, sub_mulVec, smul_mulVec, one_mulVec,
    vecMulVec_mulVec, hv]
  simp

/-! ### Planar homography -/

/-- **Planar homography**: if `X₁` lies on the plane `n ⬝ᵥ X = d` (`d ≠ 0`) and `X₂ = R X₁ + t`,
then `X₂ = (R + (1/d) t nᵀ) X₁`. -/
theorem planar_homography (R : Matrix (Fin 3) (Fin 3) ℝ) (t n X1 X2 : Fin 3 → ℝ) {d : ℝ}
    (hd : d ≠ 0) (hplane : n ⬝ᵥ X1 = d) (h : X2 = R *ᵥ X1 + t) :
    X2 = (R + (1 / d) • vecMulVec t n) *ᵥ X1 := by
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, hplane, h]
  congr 1
  ext i
  simp [hd]

/-! ### Triangulation -/

/-- **Triangulation uniqueness**: if `x₂` and `R x₁` are linearly independent (the back-projected
rays are not parallel), the depths `(a, b)` with `b x₂ = R (a x₁) + t` are unique. -/
theorem triangulation_unique (R : Matrix (Fin 3) (Fin 3) ℝ) (t x1 x2 : Fin 3 → ℝ)
    (hind : LinearIndependent ℝ ![x2, R *ᵥ x1]) {a b a' b' : ℝ}
    (h : b • x2 = R *ᵥ (a • x1) + t) (h' : b' • x2 = R *ᵥ (a' • x1) + t) :
    a = a' ∧ b = b' := by
  rw [mulVec_smul] at h h'
  have key : (b - b') • x2 + (a' - a) • (R *ᵥ x1) = 0 := by
    rw [sub_smul, sub_smul, h, h']; abel
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hind _ _ key
  exact ⟨(sub_eq_zero.mp h2).symm, sub_eq_zero.mp h1⟩

end RoboLean.Epipolar
