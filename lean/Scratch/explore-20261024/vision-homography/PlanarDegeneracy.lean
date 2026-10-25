import ControlsLean.Vision.Homography
import ControlsLean.Vision.EightPoint
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

open Matrix

namespace VisionExplore
open ControlsLean.Vision

variable {K : Type*} [Field K]

/-! ### 1. When is the plane-induced homography invertible? -/

/-- **Matrix determinant lemma for the plane-induced homography**:
`det (R + d⁻¹ t nᵀ) = det R + d⁻¹ · nᵀ adj(R) t`. -/
theorem det_homographyPlane (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d : K) :
    (homographyPlane R t n d).det = R.det + d⁻¹ * (n ⬝ᵥ (adjugate R *ᵥ t)) := by
  simp only [homographyPlane, det_fin_three, adjugate_fin_three, outerProduct, mulVec,
    dotProduct, Fin.sum_univ_three]
  simp
  ring

/-- For a rotation (`Rᵀ R = 1`, `det R = 1`), `det H = 1 + d⁻¹ · n ⬝ (Rᵀ t)`. -/
theorem det_homographyPlane_rotation (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d : K)
    (hR : Rᵀ * R = 1) (hdet : R.det = 1) :
    (homographyPlane R t n d).det = 1 + d⁻¹ * (n ⬝ᵥ (Rᵀ *ᵥ t)) := by
  have hadj : adjugate R = Rᵀ := by
    have h1 : R⁻¹ = adjugate R := by rw [inv_def, hdet]; simp
    rw [← h1, inv_eq_left_inv hR]
  rw [det_homographyPlane, hadj, hdet]

/-- **Geometric meaning.** For a rotation and `d ≠ 0`, `H = R + d⁻¹ t nᵀ` is singular iff the
centre of camera 2, `C₂ = -Rᵀ t` (in camera-1 coordinates), lies on the plane `n ⬝ X = d`. -/
theorem homographyPlane_singular_iff (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d : K)
    (hR : Rᵀ * R = 1) (hdet : R.det = 1) (hd : d ≠ 0) :
    (homographyPlane R t n d).det = 0 ↔ n ⬝ᵥ (-(Rᵀ *ᵥ t)) = d := by
  rw [det_homographyPlane_rotation R t n d hR hdet, dotProduct_neg]
  constructor
  · intro h
    have := congrArg (d * ·) h
    field_simp at this
    linear_combination -this
  · intro h
    have h' : n ⬝ᵥ (Rᵀ *ᵥ t) = -d := by linear_combination -h
    rw [h']; field_simp; ring

/-! ### 2. `E = [t]ₓ H` for any plane -/

theorem skew_mul_outerProduct_self (t n : Fin 3 → K) : skew t * outerProduct t n = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew, outerProduct, mul_apply, Fin.sum_univ_three] <;> ring

/-- The essential matrix factors through *every* plane-induced homography: `[t]ₓ R = [t]ₓ H`. -/
theorem essential_eq_skew_mul_homographyPlane (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K)
    (d : K) : essential R t = skew t * homographyPlane R t n d := by
  rw [essential, homographyPlane, Matrix.mul_add, Matrix.mul_smul, skew_mul_outerProduct_self,
    smul_zero, add_zero]

/-! ### 3. Coplanar scenes defeat the eight-point rank hypothesis -/

/-- If every correspondence is related by a homography (`x₂ ∝ H x₁`), then *every*
`[v]ₓ H` satisfies all epipolar constraints: a 3-parameter family of "essential" solutions. -/
theorem skew_mul_satisfies_of_homography {n : ℕ} (H : Matrix (Fin 3) (Fin 3) K)
    {x₁ x₂ : Fin n → Fin 3 → K} (hx : ∀ i, ∃ μ : K, x₂ i = μ • (H *ᵥ x₁ i)) (v : Fin 3 → K) :
    ∀ i, x₂ i ⬝ᵥ ((skew v * H) *ᵥ x₁ i) = 0 := by
  intro i
  obtain ⟨μ, hμ⟩ := hx i
  rw [hμ, ← mulVec_mulVec, skew_mulVec, smul_dotProduct, dot_cross_self, smul_zero]

/-- **Planar degeneracy of the eight-point algorithm.** If all correspondences are related by an
invertible homography, the constraint matrix can never have rank 8 (so `eq_smul_essential`
is vacuous for coplanar scenes, no matter how many points are used). -/
theorem constraintMatrix_rank_ne_eight_of_homography {n : ℕ} (H : Matrix (Fin 3) (Fin 3) K)
    (hH : H.det ≠ 0) {x₁ x₂ : Fin n → Fin 3 → K}
    (hx : ∀ i, ∃ μ : K, x₂ i = μ • (H *ᵥ x₁ i)) :
    (constraintMatrix x₁ x₂).rank ≠ 8 := by
  intro hrank
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hH
  set a : Fin 3 → K := ![1, 0, 0]
  set b : Fin 3 → K := ![0, 1, 0]
  have cancel : ∀ v, skew v * H * H⁻¹ = skew v := fun v => by
    rw [Matrix.mul_assoc, mul_nonsing_inv H hu, Matrix.mul_one]
  have hE0 : skew a * H ≠ 0 := by
    intro h
    have h2 := congrArg (· * H⁻¹) h
    simp only [cancel, Matrix.zero_mul] at h2
    have := congrFun (congrFun h2 2) 1
    simp [skew, a] at this
  obtain ⟨c, hc⟩ := eq_smul_of_rank_eq_eight hrank hE0
    (skew_mul_satisfies_of_homography H hx a) (skew_mul_satisfies_of_homography H hx b)
  have h2 := congrArg (· * H⁻¹) hc
  simp only [cancel, Matrix.smul_mul] at h2
  have := congrFun (congrFun h2 0) 2
  simp [skew, a, b] at this

/-- Corollary, in scene terms: if every scene point lies on the plane `n ⬝ X = d` (`d ≠ 0`) and
`H = R + d⁻¹ t nᵀ` is invertible, the eight-point constraint matrix never has rank 8. -/
theorem planar_scene_rank_ne_eight {n : ℕ} (R : Matrix (Fin 3) (Fin 3) K) (t nrm : Fin 3 → K)
    (d : K) (hd : d ≠ 0) (hH : (homographyPlane R t nrm d).det ≠ 0)
    {x₁ x₂ : Fin n → Fin 3 → K} {d₁ d₂ : Fin n → K} (hd₂ : ∀ i, d₂ i ≠ 0)
    (hplane : ∀ i, nrm ⬝ᵥ (d₁ i • x₁ i) = d)
    (hscene : ∀ i, d₂ i • x₂ i = R *ᵥ (d₁ i • x₁ i) + t) :
    (constraintMatrix x₁ x₂).rank ≠ 8 := by
  refine constraintMatrix_rank_ne_eight_of_homography _ hH fun i => ⟨(d₂ i)⁻¹ * d₁ i, ?_⟩
  have h := plane_homography_constraint R t nrm d (x₁ i) (x₂ i) (d₁ i) (d₂ i) hd (hplane i)
    (hscene i)
  rw [mulVec_smul] at h
  rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ (hd₂ i), one_smul]

end VisionExplore
