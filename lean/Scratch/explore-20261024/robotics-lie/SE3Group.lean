import ControlsLean.Robotics.SE3Kinematics
import Mathlib

open Matrix ControlsLean.Vision ControlsLean.Robotics

namespace RoboticsLieScratch

abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev V3 := Fin 3 → ℝ

/-- SE(3) as pairs `(R, p)` acting by `x ↦ R x + p`. -/
def se3mul (g h : M3 × V3) : M3 × V3 := (g.1 * h.1, g.2 + g.1 *ᵥ h.2)
def se3act (g : M3 × V3) (x : V3) : V3 := g.1 *ᵥ x + g.2
def se3inv (g : M3 × V3) : M3 × V3 := (g.1ᵀ, -(g.1ᵀ *ᵥ g.2))

theorem se3mul_assoc (a b c : M3 × V3) : se3mul (se3mul a b) c = se3mul a (se3mul b c) := by
  simp only [se3mul, Matrix.mul_assoc, mulVec_add, mulVec_mulVec, add_assoc]

theorem se3act_mul (g h : M3 × V3) (x : V3) : se3act (se3mul g h) x = se3act g (se3act h x) := by
  simp only [se3act, se3mul, mulVec_add, mulVec_mulVec]; abel

theorem se3inv_mul {g : M3 × V3} (hR : g.1ᵀ * g.1 = 1) : se3mul (se3inv g) g = (1, 0) := by
  simp [se3mul, se3inv, hR]

theorem se3mul_inv {g : M3 × V3} (hR : g.1 * g.1ᵀ = 1) : se3mul g (se3inv g) = (1, 0) := by
  simp [se3mul, se3inv, hR, mulVec_neg, mulVec_mulVec]

/-- Homogeneous 4×4 matrix. -/
def hom4 (g : M3 × V3) : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ :=
  fromBlocks g.1 (replicateCol (Fin 1) g.2) 0 1

theorem hom4_mul (g h : M3 × V3) : hom4 (se3mul g h) = hom4 g * hom4 h := by
  simp only [hom4, se3mul, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    Matrix.mul_one, zero_add]
  congr 1
  ext i j
  simp [replicateCol, Matrix.mul_apply, mulVec, dotProduct, add_comm]

/-- Cofactor identity and SO(3) cross-product equivariance. -/
theorem mulVec_cross_SO3 {R : M3} (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) (a b : V3) :
    R *ᵥ (a ⨯₃ b) = (R *ᵥ a) ⨯₃ (R *ᵥ b) := by
  obtain ⟨hO, hdet⟩ := mem_specialOrthogonalGroup_iff.mp hR
  have h1 : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hO
  have hadj : adjugate R = Rᵀ := by
    calc adjugate R = Rᵀ * R * adjugate R := by rw [h1, Matrix.one_mul]
      _ = Rᵀ := by rw [Matrix.mul_assoc, mul_adjugate, hdet, one_smul, Matrix.mul_one]
  have key : (R *ᵥ a) ⨯₃ (R *ᵥ b) = (adjugate R)ᵀ *ᵥ (a ⨯₃ b) := by
    ext i; fin_cases i <;>
      simp [cross_apply, mulVec, dotProduct, Fin.sum_univ_three, adjugate_fin_three] <;> ring
  rw [key, hadj, transpose_transpose]

/-- **Meaning of `adjoint6`**: a twist `(ω, v)` is the velocity field `x ↦ ω × x + v`.
Transporting the field by `g = (R, p)` gives `x ↦ R (ω × g⁻¹ x + v)`, and this equals the
velocity field of `Ad_g (ω, v)`. This validates the block convention of `adjoint6`
(lower-left `[p]× R`, twist order `(ω, v)`). -/
theorem adjoint6_velocity_field {R : M3} (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ)
    (p ω v x : V3) :
    let ξ' := adjoint6 R p *ᵥ Sum.elim ω v
    (fun i => ξ' (Sum.inl i)) ⨯₃ x + (fun i => ξ' (Sum.inr i))
      = R *ᵥ (ω ⨯₃ (Rᵀ *ᵥ (x - p)) + v) := by
  intro ξ'
  have h1 : R * Rᵀ = 1 :=
    (mem_orthogonalGroup_iff (Fin 3) ℝ).mp (mem_specialOrthogonalGroup_iff.mp hR).1
  have hl : (fun i => ξ' (Sum.inl i)) = R *ᵥ ω := by
    funext i; simp [ξ', adjoint6, fromBlocks_mulVec]
  have hr : (fun i => ξ' (Sum.inr i)) = p ⨯₃ (R *ᵥ ω) + R *ᵥ v := by
    funext i; simp [ξ', adjoint6, fromBlocks_mulVec, ← mulVec_mulVec, skew_mulVec]
  rw [hl, hr, mulVec_add, mulVec_cross_SO3 hR, mulVec_mulVec, h1, one_mulVec, map_sub,
    ← cross_anticomm (R *ᵥ ω) p]
  abel

end RoboticsLieScratch
