/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Two-view geometry: homogeneous incidence and the epipolar constraint

Points and lines of the projective image plane are represented by vectors in `Fin 3 → K`.
A point `p` lies on a line `l` iff `l ⬝ᵥ p = 0`.

For two calibrated cameras related by a rigid motion `X₂ = R X₁ + t`, the essential matrix
`E = [t]ₓ R` satisfies the epipolar constraint `x₂ᵀ E x₁ = 0` for every pair of corresponding
image points, with no assumption on `R` (it need not be a rotation).
-/

open Matrix

namespace ControlsLean.Vision

variable {K : Type*} [Field K]

/-- The skew-symmetric "cross-product matrix" `[t]ₓ`, characterised by `[t]ₓ v = t × v`. -/
def skew (t : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, -t 2, t 1; t 2, 0, -t 0; -t 1, t 0, 0]

theorem skew_mulVec (t v : Fin 3 → K) : skew t *ᵥ v = t ⨯₃ v := by
  ext i
  fin_cases i <;>
    simp [skew, cross_apply, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem skew_transpose (t : Fin 3 → K) : (skew t)ᵀ = -skew t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew]

theorem det_skew (t : Fin 3 → K) : (skew t).det = 0 := by
  simp [skew, det_fin_three]; ring

/-- The line through two image points is their cross product. -/
theorem mem_line_left (p q : Fin 3 → K) : (p ⨯₃ q) ⬝ᵥ p = 0 := by
  rw [dotProduct_comm]; exact dot_self_cross p q

theorem mem_line_right (p q : Fin 3 → K) : (p ⨯₃ q) ⬝ᵥ q = 0 := by
  rw [dotProduct_comm]; exact dot_cross_self p q

/-- Dually, the intersection of two lines is their cross product. -/
theorem intersection_mem (l m : Fin 3 → K) : l ⬝ᵥ (l ⨯₃ m) = 0 ∧ m ⬝ᵥ (l ⨯₃ m) = 0 :=
  ⟨dot_self_cross l m, dot_cross_self l m⟩

/-- Three image points are collinear iff the determinant of their coordinates vanishes. -/
theorem collinear_iff_det (p q r : Fin 3 → K) :
    p ⬝ᵥ (q ⨯₃ r) = 0 ↔ Matrix.det ![p, q, r] = 0 := by
  rw [triple_product_eq_det]

/-- The essential matrix `E = [t]ₓ R`. -/
def essential (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  skew t * R

theorem essential_mulVec (R : Matrix (Fin 3) (Fin 3) K) (t v : Fin 3 → K) :
    essential R t *ᵥ v = t ⨯₃ (R *ᵥ v) := by
  rw [essential, ← mulVec_mulVec, skew_mulVec]

/-- **Epipolar constraint.** If a scene point has depth `d₁ ≠ 0`-scaled image `x₁` in camera 1
and `d₂ ≠ 0`-scaled image `x₂` in camera 2, i.e. `d₂ x₂ = R (d₁ x₁) + t`, then `x₂ᵀ E x₁ = 0`.
Only `d₂ ≠ 0` is needed. -/
theorem epipolar_constraint (R : Matrix (Fin 3) (Fin 3) K) (t x₁ x₂ : Fin 3 → K) (d₁ d₂ : K)
    (hd₂ : d₂ ≠ 0) (h : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) :
    x₂ ⬝ᵥ (essential R t *ᵥ x₁) = 0 := by
  rw [essential_mulVec]
  have key : (d₂ • x₂) ⬝ᵥ (t ⨯₃ (R *ᵥ x₁)) = 0 := by
    rw [h, mulVec_smul, add_dotProduct, smul_dotProduct, dot_cross_self, dot_self_cross]
    simp
  rw [smul_dotProduct, smul_eq_mul, mul_eq_zero] at key
  exact key.resolve_left hd₂

/-- The essential matrix is singular, so it has rank at most 2. -/
theorem det_essential (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K) :
    (essential R t).det = 0 := by
  simp [essential, det_mul, det_skew]

/-- The translation `t` (the epipole in image 2) lies on every epipolar line `E x₁`. -/
theorem epipole_mem_epipolarLine (R : Matrix (Fin 3) (Fin 3) K) (t x₁ : Fin 3 → K) :
    t ⬝ᵥ (essential R t *ᵥ x₁) = 0 := by
  rw [essential_mulVec, dot_self_cross]

/-- Equivalently, `t` is a left null vector of `E`: `tᵀ E = 0`. -/
theorem vecMul_essential (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K) :
    t ᵥ* essential R t = 0 := by
  ext j
  have := epipole_mem_epipolarLine R t (Pi.single j 1)
  rwa [dotProduct_mulVec, dotProduct_single, mul_one] at this

end ControlsLean.Vision

#print axioms ControlsLean.Vision.epipolar_constraint
#print axioms ControlsLean.Vision.det_essential
#print axioms ControlsLean.Vision.vecMul_essential
