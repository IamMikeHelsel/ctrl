/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ControlsLean.Vision.Epipolar

/-!
# Planar Homographies, Projective Collineations, and Two-View Plane Motion

This module formalizes projective transformations of the projective plane $\mathbb{P}^2(K)$
represented by invertible $3 \times 3$ matrices $H \in \mathrm{GL}(3, K)$.

### Mathematical Background
In two-view computer vision, when scene points lie on a 3D plane $\pi = \{ X \in K^3 \mid n^\top X = d \}$,
the epipolar constraint (essential/fundamental matrix) degenerates because all epipolar lines
meet the epipole and the essential matrix $E$ cannot be uniquely determined from coplanar correspondences.
Instead, image coordinates across the two views are related by a projective collineation (homography):
$$x_2 \propto H x_1, \qquad H = R + \frac{1}{d} t n^\top.$$

### Main Results Proved:
1. `outerProduct_mulVec`: Matrix-vector multiplication for outer products $u v^\top x = (v \cdot x) u$.
2. `lineTransform_dotProduct`: Invariance of point-line incidence under projective collineation:
   $(H^{-T} l) \cdot (H p) = l \cdot p$.
3. `det_homography_three_points`: Determinant scaling for three points transformed by $H$:
   $\det [H p, H q, H r] = \det(H) \det [p, q, r]$.
4. `collinear_homography`: Collinearity preservation under any invertible homography:
   $\det [H p, H q, H r] = 0 \iff \det [p, q, r] = 0$.
5. `plane_homography_mulVec`: Plane-induced motion on 3D coordinates: $H X = R X + t$ when $n \cdot X = d$.
6. `plane_homography_constraint`: Two-view image correspondence for coplanar scene points with depths $d_1, d_2$.
-/

open Matrix

namespace ControlsLean.Vision

variable {K : Type*} [Field K]

/-- Projective homography action on image points: `homography H x = H *ᵥ x`. -/
def homography (H : Matrix (Fin 3) (Fin 3) K) (x : Fin 3 → K) : Fin 3 → K :=
  H *ᵥ x

/-- Outer product `u vᵀ` as a $3 \times 3$ matrix: `(outerProduct u v) i j = u i * v j`. -/
def outerProduct (u v : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => u i * v j

@[simp]
theorem outerProduct_apply (u v : Fin 3 → K) (i j : Fin 3) :
    outerProduct u v i j = u i * v j := rfl

/-- Matrix-vector multiplication for an outer product matrix: `(u vᵀ) x = (v ⬝ᵥ x) • u`. -/
theorem outerProduct_mulVec (u v x : Fin 3 → K) :
    outerProduct u v *ᵥ x = (v ⬝ᵥ x) • u := by
  ext i
  simp [outerProduct, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Line transformation under a projective homography `H` with inverse `H_inv`:
a line `l` transforms contragrediently by `l' = (H_inv)ᵀ *ᵥ l`. -/
def lineTransform (H_inv : Matrix (Fin 3) (Fin 3) K) (l : Fin 3 → K) : Fin 3 → K :=
  H_invᵀ *ᵥ l

/-- **Duality of lines and points under homographies** (Hartley & Zisserman Theorem 2.1):
Incidence between points and lines is invariant under projective transformations:
`((H_inv)ᵀ l) ⬝ᵥ (H p) = l ⬝ᵥ p` whenever `H_inv * H = 1`. -/
theorem lineTransform_dotProduct (H H_inv : Matrix (Fin 3) (Fin 3) K)
    (hinv : H_inv * H = 1) (l p : Fin 3 → K) :
    (lineTransform H_inv l) ⬝ᵥ (H *ᵥ p) = l ⬝ᵥ p := by
  unfold lineTransform
  rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul, hinv, vecMul_one]

/-- Incidence preservation: `p` lies on line `l` iff `H *ᵥ p` lies on `lineTransform H_inv l`. -/
theorem mem_lineTransform_iff (H H_inv : Matrix (Fin 3) (Fin 3) K)
    (hinv : H_inv * H = 1) (l p : Fin 3 → K) :
    (lineTransform H_inv l) ⬝ᵥ (H *ᵥ p) = 0 ↔ l ⬝ᵥ p = 0 := by
  rw [lineTransform_dotProduct H H_inv hinv l p]

/-- **Determinant scaling under projective transformation**:
The determinant of three transformed 3D points is scaled by $\det(H)$:
$\det [H p, H q, H r] = \det(H) \det [p, q, r]$. -/
theorem det_homography_three_points (H : Matrix (Fin 3) (Fin 3) K) (p q r : Fin 3 → K) :
    (Matrix.of ![H *ᵥ p, H *ᵥ q, H *ᵥ r]).det = H.det * (Matrix.of ![p, q, r]).det := by
  rw [det_fin_three (Matrix.of ![H *ᵥ p, H *ᵥ q, H *ᵥ r]),
      det_fin_three (Matrix.of ![p, q, r]),
      det_fin_three H]
  simp [mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- **Collinearity preservation under projective collineation** (Hartley & Zisserman Result 2.3):
For an invertible homography matrix `H` (`H.det ≠ 0`), three points `p, q, r` are collinear
if and only if their transformed images `H p, H q, H r` are collinear. -/
theorem collinear_homography (H : Matrix (Fin 3) (Fin 3) K) (hH : H.det ≠ 0)
    (p q r : Fin 3 → K) :
    (Matrix.of ![H *ᵥ p, H *ᵥ q, H *ᵥ r]).det = 0 ↔ (Matrix.of ![p, q, r]).det = 0 := by
  rw [det_homography_three_points, mul_eq_zero]
  exact ⟨fun h => h.resolve_left hH, fun h => Or.inr h⟩

/-- Homography matrix induced by a plane with normal `n` and perpendicular distance `d`:
`H = R + (1 / d) • (t ⊗ n)`. -/
def homographyPlane (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d : K) :
    Matrix (Fin 3) (Fin 3) K :=
  R + d⁻¹ • outerProduct t n

/-- Alternative parameterized definition taking the inverse distance `d_inv = 1 / d`. -/
def planeHomography (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d_inv : K) :
    Matrix (Fin 3) (Fin 3) K :=
  R + d_inv • outerProduct t n

theorem homographyPlane_eq_planeHomography (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d : K) :
    homographyPlane R t n d = planeHomography R t n (d⁻¹) := rfl

/-- **Plane-induced 3D motion**:
For every 3D point `X` lying on the plane `n ⬝ᵥ X = d` with `d ≠ 0`,
the plane homography satisfies `H X = R X + t`. -/
theorem plane_homography_mulVec (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d : K)
    (X : Fin 3 → K) (h_plane : n ⬝ᵥ X = d) (hd : d ≠ 0) :
    homographyPlane R t n d *ᵥ X = R *ᵥ X + t := by
  simp [homographyPlane, add_mulVec, smul_mulVec, outerProduct_mulVec, h_plane]
  rw [smul_smul, inv_mul_cancel₀ hd, one_smul]

/-- **Two-view planar image correspondence** (Hartley & Zisserman Theorem 13.1):
If a 3D point on plane `n ⬝ᵥ (d₁ • x₁) = d` projectively projects to `x₁` in camera 1 (with depth `d₁`)
and to `x₂` in camera 2 (with depth `d₂` and relative pose `(R, t)`), i.e.,
`d₂ • x₂ = R (d₁ • x₁) + t`,
then the image rays satisfy the exact linear homography relation:
`d₂ • x₂ = H (d₁ • x₁)`. -/
theorem plane_homography_constraint (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d : K)
    (x₁ x₂ : Fin 3 → K) (d₁ d₂ : K) (hd : d ≠ 0)
    (h_plane : n ⬝ᵥ (d₁ • x₁) = d)
    (h_rigid : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) :
    d₂ • x₂ = homographyPlane R t n d *ᵥ (d₁ • x₁) := by
  rw [plane_homography_mulVec R t n d (d₁ • x₁) h_plane hd, h_rigid]

/-- Projection form using `planeHomography` with parameter `d_inv = d⁻¹`. -/
theorem planeHomography_constraint (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d : K)
    (x₁ x₂ : Fin 3 → K) (d₁ d₂ : K) (hd : d ≠ 0)
    (h_plane : n ⬝ᵥ (d₁ • x₁) = d)
    (h_rigid : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) :
    d₂ • x₂ = planeHomography R t n (d⁻¹) *ᵥ (d₁ • x₁) := by
  rw [← homographyPlane_eq_planeHomography]
  exact plane_homography_constraint R t n d x₁ x₂ d₁ d₂ hd h_plane h_rigid

/-- Identity homography acts trivially on rays. -/
theorem homography_one (x : Fin 3 → K) :
    homography (1 : Matrix (Fin 3) (Fin 3) K) x = x := by
  simp [homography]

/-- Composition of homographies corresponds to matrix multiplication. -/
theorem homography_mul (H₁ H₂ : Matrix (Fin 3) (Fin 3) K) (x : Fin 3 → K) :
    homography (H₁ * H₂) x = homography H₁ (homography H₂ x) := by
  simp [homography, mulVec_mulVec]

end ControlsLean.Vision


