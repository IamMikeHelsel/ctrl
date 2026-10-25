import Mathlib

/-!
Scratch: pinhole camera `x = K [R | t] X`. Algebraic facts over an arbitrary field.
-/

open Matrix

namespace PinholeScratch

variable {𝕜 : Type*} [Field 𝕜]

abbrev M3 (𝕜 : Type*) := Matrix (Fin 3) (Fin 3) 𝕜
abbrev V3 (𝕜 : Type*) := Fin 3 → 𝕜

/-- Homogeneous world point `(X, w)` in `𝕜^3 ⊕ 𝕜^1`. -/
def hom (X : V3 𝕜) (w : 𝕜) : (Fin 3 ⊕ Fin 1) → 𝕜 := Sum.elim X (fun _ => w)

/-- The 3×4 camera matrix `P = K [R | t]`. -/
def camera (K R : M3 𝕜) (t : V3 𝕜) : Matrix (Fin 3) (Fin 3 ⊕ Fin 1) 𝕜 :=
  K * Matrix.fromCols R (Matrix.replicateCol (Fin 1) t)

theorem camera_mulVec (K R : M3 𝕜) (t X : V3 𝕜) (w : 𝕜) :
    camera K R t *ᵥ hom X w = K *ᵥ (R *ᵥ X + w • t) := by
  unfold camera
  rw [← mulVec_mulVec]
  congr 1
  ext i
  simp [mulVec, dotProduct, hom, Fintype.sum_sum_type, fromCols, replicateCol, mul_comm]

/-- Camera center `C = -Rᵀ t` (for orthogonal `R`). -/
def center (R : M3 𝕜) (t : V3 𝕜) : V3 𝕜 := -(Rᵀ *ᵥ t)

/-- The camera center is in the kernel of `P`: `P C̃ = 0`. -/
theorem camera_center (K R : M3 𝕜) (t : V3 𝕜) (hR : R * Rᵀ = 1) :
    camera K R t *ᵥ hom (center R t) 1 = 0 := by
  rw [camera_mulVec, center, mulVec_neg, mulVec_mulVec, hR, one_mulVec, one_smul,
    neg_add_cancel, mulVec_zero]

/-- The kernel of `P` is exactly the line through the homogeneous camera center
(needs `K` invertible). -/
theorem camera_mulVec_eq_zero_iff (K R : M3 𝕜) (t X : V3 𝕜) (w : 𝕜)
    (hR : R * Rᵀ = 1) (hRt : Rᵀ * R = 1) (hK : IsUnit K.det) :
    camera K R t *ᵥ hom X w = 0 ↔ X = w • center R t := by
  rw [camera_mulVec]
  constructor
  · intro h
    have h1 : R *ᵥ X + w • t = 0 := by
      have := congrArg (fun v => K⁻¹ *ᵥ v) h
      simpa [mulVec_mulVec, nonsing_inv_mul K hK] using this
    have h2 : X = Rᵀ *ᵥ (R *ᵥ X) := by rw [mulVec_mulVec, hRt, one_mulVec]
    rw [h2, eq_neg_of_add_eq_zero_left h1, center, mulVec_neg, mulVec_smul, smul_neg]
  · rintro rfl
    rw [center, smul_neg, mulVec_neg, mulVec_smul, mulVec_mulVec, hR, one_mulVec,
      neg_add_cancel, mulVec_zero]

/-! ### Lines and vanishing points -/

/-- Projection of the 3D line `X₀ + s d` is affine in `s`:
`P (X₀ + s d) = P X₀ + s (K R d)`. -/
theorem project_line (K R : M3 𝕜) (t X₀ d : V3 𝕜) (s : 𝕜) :
    camera K R t *ᵥ hom (X₀ + s • d) 1 =
      camera K R t *ᵥ hom X₀ 1 + s • (K *ᵥ (R *ᵥ d)) := by
  simp only [camera_mulVec, mulVec_add, mulVec_smul]
  abel

/-- The point at infinity in direction `d` projects to the vanishing point `K R d`,
independent of `t`. -/
theorem project_point_at_infinity (K R : M3 𝕜) (t d : V3 𝕜) :
    camera K R t *ᵥ hom d 0 = K *ᵥ (R *ᵥ d) := by
  simp [camera_mulVec]

theorem det_three_affine (u v : V3 𝕜) (a b c : 𝕜) :
    Matrix.det (Matrix.of ![u + a • v, u + b • v, u + c • v]) = 0 := by
  rw [Matrix.det_fin_three]
  simp
  ring

theorem det_affine_vanishing (u v : V3 𝕜) (a b : 𝕜) :
    Matrix.det (Matrix.of ![u + a • v, u + b • v, v]) = 0 := by
  rw [Matrix.det_fin_three]
  simp
  ring

/-- **Image of a line is a line**: any three points on a 3D line project to collinear
image points (possibly degenerate). -/
theorem image_of_line_collinear (K R : M3 𝕜) (t X₀ d : V3 𝕜) (a b c : 𝕜) :
    Matrix.det (Matrix.of ![camera K R t *ᵥ hom (X₀ + a • d) 1, camera K R t *ᵥ hom (X₀ + b • d) 1,
      camera K R t *ᵥ hom (X₀ + c • d) 1]) = 0 := by
  simp only [project_line]
  exact det_three_affine (𝕜 := 𝕜) _ _ _ _ _

/-- **Parallel lines share a vanishing point**: for every line with direction `d`
(any base point `X₀`), the image line through two of its points also passes through
`v = K R d`. -/
theorem vanishing_point_on_image_line (K R : M3 𝕜) (t X₀ d : V3 𝕜) (a b : 𝕜) :
    Matrix.det (Matrix.of ![camera K R t *ᵥ hom (X₀ + a • d) 1, camera K R t *ᵥ hom (X₀ + b • d) 1,
      K *ᵥ (R *ᵥ d)]) = 0 := by
  simp only [project_line]
  exact det_affine_vanishing (𝕜 := 𝕜) _ _ _ _

/-- Degenerate case (a "dumb question" answered): a 3D line through the camera centre
images to a single projective point — every image is a multiple of `K R d`. -/
theorem line_through_center_images_to_point (K R : M3 𝕜) (t d : V3 𝕜) (hR : R * Rᵀ = 1)
    (s : 𝕜) :
    camera K R t *ᵥ hom (center R t + s • d) 1 = s • (K *ᵥ (R *ᵥ d)) := by
  rw [project_line, camera_center K R t hR, zero_add]

/-- Orthogonal matrices preserve the dot product. -/
theorem dot_mulVec_orth (R : M3 𝕜) (hRt : Rᵀ * R = 1) (x y : V3 𝕜) :
    (R *ᵥ x) ⬝ᵥ (R *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hRt, one_mulVec]

/-- `(K a) ⬝ (K⁻ᵀ b) = a ⬝ b` for invertible `K`. -/
theorem dot_mulVec_invT (K : M3 𝕜) (hK : IsUnit K.det) (a b : V3 𝕜) :
    (K *ᵥ a) ⬝ᵥ (K⁻¹ᵀ *ᵥ b) = a ⬝ᵥ b := by
  rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, nonsing_inv_mul K hK, one_mulVec]

/-- Vanishing points of directions orthogonal to the plane normal `n` lie on the
vanishing line `l = K⁻ᵀ R n` (needs `R` orthogonal, `K` invertible). -/
theorem vanishing_line (K R : M3 𝕜) (n d : V3 𝕜) (hRt : Rᵀ * R = 1) (hK : IsUnit K.det)
    (hd : d ⬝ᵥ n = 0) :
    (K *ᵥ (R *ᵥ d)) ⬝ᵥ (K⁻¹ᵀ *ᵥ (R *ᵥ n)) = 0 := by
  rw [dot_mulVec_invT K hK, dot_mulVec_orth R hRt, hd]

/-- **Image of the absolute conic**: vanishing points `vᵢ = K R dᵢ` satisfy
`v₁ ⬝ (ω v₂) = d₁ ⬝ d₂` with `ω = K⁻ᵀ K⁻¹`; orthogonal directions give the classical
calibration constraint `v₁ᵀ ω v₂ = 0`. -/
theorem iac_constraint (K R : M3 𝕜) (d₁ d₂ : V3 𝕜) (hRt : Rᵀ * R = 1) (hK : IsUnit K.det) :
    (K *ᵥ (R *ᵥ d₁)) ⬝ᵥ ((K⁻¹ᵀ * K⁻¹) *ᵥ (K *ᵥ (R *ᵥ d₂))) = d₁ ⬝ᵥ d₂ := by
  rw [← mulVec_mulVec, mulVec_mulVec _ K⁻¹ K, nonsing_inv_mul K hK, one_mulVec,
    dot_mulVec_invT K hK, dot_mulVec_orth R hRt]

end PinholeScratch
