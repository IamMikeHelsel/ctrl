import ControlsLean.Vision.Homography
import Mathlib.Tactic
noncomputable section
namespace V01Determinant
open Matrix ControlsLean.Vision
variable {K : Type*} [Field K]

theorem rank_one_det (u n : Fin 3 → K) (a : K) :
    (1+a • outerProduct u n).det=1+a*(n ⬝ᵥ u) := by
  rw [det_fin_three]
  simp [outerProduct, dotProduct, Fin.sum_univ_three]
  ring

theorem transport_outer (R : Matrix (Fin 3) (Fin 3) K) (y n : Fin 3 → K) :
    R*outerProduct y n=outerProduct (R*ᵥy) n := by
  ext i j
  simp [Matrix.mul_apply, outerProduct, mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem factor (R : Matrix (Fin 3) (Fin 3) K) (t n y : Fin 3 → K) (d : K)
    (hy : R*ᵥy=t) : homographyPlane R t n d=R*(1+d⁻¹ • outerProduct y n) := by
  rw [mul_add, mul_one, Matrix.mul_smul, transport_outer, hy]
  rfl

theorem determinant (R : Matrix (Fin 3) (Fin 3) K) (t n y : Fin 3 → K) (d : K)
    (hy : R*ᵥy=t) :
    (homographyPlane R t n d).det=R.det*(1+d⁻¹*(n ⬝ᵥ y)) := by
  rw [factor R t n y d hy, det_mul, rank_one_det]

/-- If R is invertible, -y is camera2's center in camera1 coordinates. -/
theorem singular_iff_center_on_plane (R : Matrix (Fin 3) (Fin 3) K)
    (t n y : Fin 3 → K) (d : K) (hy : R*ᵥy=t) (hR : R.det≠0) (hd : d≠0) :
    (homographyPlane R t n d).det=0 ↔ n ⬝ᵥ (-y)=d := by
  rw [determinant R t n y d hy, mul_eq_zero]
  simp only [hR, false_or, dotProduct_neg]
  have hs : 1+d⁻¹*(n ⬝ᵥ y)=(d+n ⬝ᵥ y)/d := by field_simp
  rw [hs, div_eq_zero_iff]
  simp only [hd, or_false]
  constructor <;> intro h <;> linear_combination -h

 theorem center_identity (R : Matrix (Fin 3) (Fin 3) K) (t y : Fin 3 → K)
    (hy : R*ᵥy=t) : R*ᵥ(-y)+t=0 := by simp [mulVec_neg,hy]
end V01Determinant
#print axioms V01Determinant.rank_one_det
#print axioms V01Determinant.transport_outer
#print axioms V01Determinant.factor
#print axioms V01Determinant.determinant
#print axioms V01Determinant.singular_iff_center_on_plane
#print axioms V01Determinant.center_identity
