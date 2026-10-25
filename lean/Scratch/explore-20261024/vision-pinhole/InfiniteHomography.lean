import Mathlib

/-!
Scratch: infinite homography, depth scaling, and vanishing points as limits.
Self-contained (re-declares `camera`/`hom` from `Pinhole.lean`).
-/

open Matrix Filter Topology

namespace PinholeScratch2

variable {𝕜 : Type*} [Field 𝕜]

abbrev M3 (𝕜 : Type*) := Matrix (Fin 3) (Fin 3) 𝕜
abbrev V3 (𝕜 : Type*) := Fin 3 → 𝕜

def hom (X : V3 𝕜) (w : 𝕜) : (Fin 3 ⊕ Fin 1) → 𝕜 := Sum.elim X (fun _ => w)

def camera (K R : M3 𝕜) (t : V3 𝕜) : Matrix (Fin 3) (Fin 3 ⊕ Fin 1) 𝕜 :=
  K * Matrix.fromCols R (Matrix.replicateCol (Fin 1) t)

theorem camera_mulVec (K R : M3 𝕜) (t X : V3 𝕜) (w : 𝕜) :
    camera K R t *ᵥ hom X w = K *ᵥ (R *ᵥ X + w • t) := by
  unfold camera
  rw [← mulVec_mulVec]
  congr 1
  ext i
  simp [mulVec, dotProduct, hom, Fintype.sum_sum_type, fromCols, replicateCol, mul_comm]

/-- **Infinite homography.** Two cameras `Pᵢ = Kᵢ [Rᵢ | -Rᵢ C]` sharing the centre `C`
are related, for *every* homogeneous world point (any depth, including points at
infinity), by the 3×3 matrix `H∞ = K₂ R₂ R₁ᵀ K₁⁻¹`. -/
theorem infinite_homography (K₁ K₂ R₁ R₂ : M3 𝕜) (C X : V3 𝕜) (w : 𝕜)
    (hR₁ : R₁ᵀ * R₁ = 1) (hK₁ : IsUnit K₁.det) :
    camera K₂ R₂ (-(R₂ *ᵥ C)) *ᵥ hom X w =
      (K₂ * R₂ * R₁ᵀ * K₁⁻¹) *ᵥ (camera K₁ R₁ (-(R₁ *ᵥ C)) *ᵥ hom X w) := by
  simp only [camera_mulVec, mulVec_mulVec]
  have e : K₂ * R₂ * R₁ᵀ * K₁⁻¹ * K₁ = K₂ * R₂ * (R₁ᵀ * R₁) * R₁ᵀ := by
    rw [hR₁, Matrix.mul_one, Matrix.mul_assoc, nonsing_inv_mul K₁ hK₁, Matrix.mul_one]
  rw [e]
  simp only [← mulVec_mulVec, hR₁, one_mulVec, smul_neg, mulVec_add, mulVec_neg,
    mulVec_smul]
  simp only [mulVec_mulVec, hR₁, one_mulVec]

/-- Pure rotation about the optical centre with fixed intrinsics: `x₂ = K R K⁻¹ x₁`,
independent of the depth of the point (no parallax). -/
theorem pure_rotation_homography (K R : M3 𝕜) (X : V3 𝕜) (w : 𝕜) (hK : IsUnit K.det) :
    camera K R 0 *ᵥ hom X w = (K * R * K⁻¹) *ᵥ (camera K 1 0 *ᵥ hom X w) := by
  have := infinite_homography K K 1 R 0 X w (by simp) hK
  simpa [Matrix.mul_one] using this

/-- No parallax under pure rotation: scaling the world point (moving it along its ray)
scales the image in view 2 by the same factor, i.e. the projective image is unchanged. -/
theorem pure_rotation_no_parallax (K R : M3 𝕜) (X : V3 𝕜) (c : 𝕜) :
    camera K R 0 *ᵥ hom (c • X) 1 = c • (camera K R 0 *ᵥ hom X 1) := by
  simp [camera_mulVec, mulVec_smul]

/-! ### Depth scaling (real) -/

/-- Inhomogeneous image coordinates. -/
noncomputable def dehom (x : V3 ℝ) : Fin 2 → ℝ := ![x 0 / x 2, x 1 / x 2]

/-- Standard intrinsic matrix with skew `s`. -/
def intrinsic (fx fy s cx cy : ℝ) : M3 ℝ := !![fx, s, cx; 0, fy, cy; 0, 0, 1]

theorem dehom_intrinsic (fx fy s cx cy x y Z : ℝ) (hZ : Z ≠ 0) :
    dehom (intrinsic fx fy s cx cy *ᵥ ![x, y, Z]) =
      ![cx, cy] + Z⁻¹ • ![fx * x + s * y, fy * y] := by
  ext i
  fin_cases i <;>
    simp [dehom, intrinsic, mulVec, dotProduct, Fin.sum_univ_three] <;> field_simp <;> ring

/-- **Doubling the depth halves the image offset** from the principal point. -/
theorem double_depth_halves (fx fy s cx cy x y Z : ℝ) (hZ : Z ≠ 0) :
    dehom (intrinsic fx fy s cx cy *ᵥ ![x, y, 2 * Z]) - ![cx, cy] =
      (1 / 2 : ℝ) • (dehom (intrinsic fx fy s cx cy *ᵥ ![x, y, Z]) - ![cx, cy]) := by
  rw [dehom_intrinsic _ _ _ _ _ _ _ _ (mul_ne_zero two_ne_zero hZ),
    dehom_intrinsic _ _ _ _ _ _ _ _ hZ]
  simp only [add_sub_cancel_left, smul_smul]
  congr 1
  field_simp

/-- Image *size* of a fronto-parallel segment at depth `Z` is `(1/Z)·(K-part)`: the
image of a segment of lateral extent `(Δx, Δy)` scales as `1/Z`. -/
theorem image_size_inv_depth (fx fy s cx cy x₁ y₁ x₂ y₂ Z : ℝ) (hZ : Z ≠ 0) :
    dehom (intrinsic fx fy s cx cy *ᵥ ![x₁, y₁, Z]) -
        dehom (intrinsic fx fy s cx cy *ᵥ ![x₂, y₂, Z]) =
      Z⁻¹ • ![fx * (x₁ - x₂) + s * (y₁ - y₂), fy * (y₁ - y₂)] := by
  rw [dehom_intrinsic _ _ _ _ _ _ _ _ hZ, dehom_intrinsic _ _ _ _ _ _ _ _ hZ]
  ext i
  fin_cases i <;> simp <;> ring

/-! ### Vanishing point as a limit -/

theorem tendsto_ratio_affine (a b c d : ℝ) (hd : d ≠ 0) :
    Tendsto (fun s : ℝ => (a + s * b) / (c + s * d)) atTop (𝓝 (b / d)) := by
  have h0 : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hnum : Tendsto (fun s : ℝ => a * s⁻¹ + b) atTop (𝓝 (b)) := by
    simpa using (h0.const_mul a).add_const b
  have hden : Tendsto (fun s : ℝ => c * s⁻¹ + d) atTop (𝓝 (d)) := by
    simpa using (h0.const_mul c).add_const d
  refine (hnum.div hden hd).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have : s ≠ 0 := hs.ne'
  show (a * s⁻¹ + b) / (c * s⁻¹ + d) = _
  rw [← mul_div_mul_left (a * s⁻¹ + b) (c * s⁻¹ + d) this]
  congr 1 <;> field_simp

/-- **Vanishing point as a limit.** If the vanishing point `v = K R d` is finite
(`v 2 ≠ 0`), the inhomogeneous image of `X₀ + s d` converges to `dehom v` as `s → ∞`,
for every base point `X₀` (so all parallel lines converge to the same image point). -/
theorem tendsto_vanishing_point (K R : M3 ℝ) (t X₀ d : V3 ℝ)
    (hv : (K *ᵥ (R *ᵥ d)) 2 ≠ 0) :
    Tendsto (fun s : ℝ => dehom (camera K R t *ᵥ hom (X₀ + s • d) 1)) atTop
      (𝓝 (dehom (K *ᵥ (R *ᵥ d)))) := by
  set u := camera K R t *ᵥ hom X₀ 1
  set v := K *ᵥ (R *ᵥ d)
  have hline : ∀ s : ℝ, camera K R t *ᵥ hom (X₀ + s • d) 1 = u + s • v := by
    intro s
    simp only [u, v, camera_mulVec, mulVec_add, mulVec_smul, one_smul]
    abel
  simp only [hline]
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · simpa [dehom] using tendsto_ratio_affine (u 0) (v 0) (u 2) (v 2) hv
  · simpa [dehom] using tendsto_ratio_affine (u 1) (v 1) (u 2) (v 2) hv

/-- With the standard intrinsic matrix (last row `0 0 1`), the third homogeneous coordinate
is untouched: the vanishing point of `d` is at infinity iff `(R d) 2 = 0`, i.e. iff `d`
is parallel to the image plane — independent of `K`. -/
theorem intrinsic_mulVec_two (fx fy s cx cy : ℝ) (v : V3 ℝ) :
    (intrinsic fx fy s cx cy *ᵥ v) 2 = v 2 := by
  simp [intrinsic, mulVec, dotProduct, Fin.sum_univ_three]

/-- "Doubling depth halves image size" is FALSE for segments extended in depth: with
`f = 1`, the axial-offset segment from depth 1 to 2 (at lateral offset 1) has image length
`1/2`; pushed back so its near end is at depth 2 (depth 2 to 3) its image length is `1/6`,
not `1/4`. -/
theorem depth_doubling_counterexample :
    ((1 : ℝ) / 1 - 1 / 2) = 1 / 2 ∧ ((1 : ℝ) / 2 - 1 / 3) = 1 / 6 ∧ (1 / 6 : ℝ) ≠ (1 / 2) / 2 := by
  norm_num

end PinholeScratch2
