import ControlsLean.Robotics.SO3Rodrigues
import Mathlib

open Matrix ControlsLean.Vision ControlsLean.Robotics

namespace RoboticsLieScratch

/-! ### Quaternion → rotation matrix -/

/-- Standard (Hamilton) quaternion-to-rotation-matrix map, `q = a + b i + c j + d k`. -/
def quatRot (q : Quaternion ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q.re^2 + q.imI^2 - q.imJ^2 - q.imK^2, 2*(q.imI*q.imJ - q.re*q.imK), 2*(q.imI*q.imK + q.re*q.imJ);
     2*(q.imI*q.imJ + q.re*q.imK), q.re^2 - q.imI^2 + q.imJ^2 - q.imK^2, 2*(q.imJ*q.imK - q.re*q.imI);
     2*(q.imI*q.imK - q.re*q.imJ), 2*(q.imJ*q.imK + q.re*q.imI), q.re^2 - q.imI^2 - q.imJ^2 + q.imK^2]

/-- Double cover: `q` and `-q` give the same rotation. -/
theorem quatRot_neg (q : Quaternion ℝ) : quatRot (-q) = quatRot q := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quatRot]

/-- `quatRot` really is conjugation `v ↦ q v q⋆` on pure quaternions `p = (0, v)`. -/
theorem quatRot_mulVec (q p : Quaternion ℝ) (v : Fin 3 → ℝ)
    (h0 : p.re = 0) (h1 : p.imI = v 0) (h2 : p.imJ = v 1) (h3 : p.imK = v 2) :
    quatRot q *ᵥ v = ![(q * p * star q).imI, (q * p * star q).imJ, (q * p * star q).imK] := by
  ext i; fin_cases i <;>
    simp [quatRot, mulVec, dotProduct, Fin.sum_univ_three, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_mul, h0, h1, h2, h3] <;> ring

/-- Multiplicativity: `quatRot` is a monoid hom `ℍ → M₃(ℝ)`. -/
theorem quatRot_mul (p q : Quaternion ℝ) : quatRot (p * q) = quatRot p * quatRot q := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [quatRot, Matrix.mul_apply, Fin.sum_univ_three, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_mul] <;> ring

theorem det_quatRot (q : Quaternion ℝ) :
    (quatRot q).det = (Quaternion.normSq q) ^ 3 := by
  rw [Quaternion.normSq_def']
  simp [quatRot, det_fin_three]; ring

theorem quatRot_mul_transpose (q : Quaternion ℝ) :
    quatRot q * (quatRot q)ᵀ = (Quaternion.normSq q) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [Quaternion.normSq_def']
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [quatRot, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- Unit quaternions land in SO(3). -/
theorem quatRot_mem_SO3 (q : Quaternion ℝ) (hq : Quaternion.normSq q = 1) :
    quatRot q ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff, det_quatRot, hq]
  refine ⟨?_, by norm_num⟩
  have := quatRot_mul_transpose q
  rw [hq] at this
  simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this

/-- Polynomial form: `quatRot q = (a² - ‖v‖²) I + 2a [v]× + 2 v vᵀ`. -/
theorem quatRot_eq (q : Quaternion ℝ) :
    quatRot q = (q.re^2 - (q.imI^2 + q.imJ^2 + q.imK^2)) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + (2 * q.re) • skew ![q.imI, q.imJ, q.imK]
      + (2 : ℝ) • vecMulVec ![q.imI, q.imJ, q.imK] ![q.imI, q.imJ, q.imK] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [quatRot, skew] <;> ring

/-- **Quaternion ↔ Rodrigues**: `q = (cos φ, sin φ · ω)` gives `R(ω, 2φ)` for unit ω. -/
theorem quatRot_axisAngle (ω : Fin 3 → ℝ) (hω : ω ⬝ᵥ ω = 1) (φ : ℝ) (q : Quaternion ℝ)
    (h0 : q.re = Real.cos φ) (h1 : q.imI = Real.sin φ * ω 0) (h2 : q.imJ = Real.sin φ * ω 1)
    (h3 : q.imK = Real.sin φ * ω 2) :
    quatRot q = rodrigues ω (2 * φ) := by
  have hω' : ω 0 ^ 2 + ω 1 ^ 2 + ω 2 ^ 2 = 1 := by
    simp [dotProduct, Fin.sum_univ_three] at hω; nlinarith [hω]
  have hv : (![Real.sin φ * ω 0, Real.sin φ * ω 1, Real.sin φ * ω 2] : Fin 3 → ℝ)
      = Real.sin φ • ω := by
    ext i; fin_cases i <;> simp
  have hskew : skew (Real.sin φ • ω) = Real.sin φ • skew ω := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [skew]
  rw [quatRot_eq, h0, h1, h2, h3]
  rw [hv, hskew, rodrigues, skew_sq, hω, vecMulVec_smul, smul_vecMulVec, smul_smul, smul_smul,
    smul_smul]
  have hn : (Real.sin φ * ω 0) ^ 2 + (Real.sin φ * ω 1) ^ 2 + (Real.sin φ * ω 2) ^ 2
      = Real.sin φ ^ 2 := by
    linear_combination Real.sin φ ^ 2 * hω'
  rw [hn, Real.sin_two_mul, Real.cos_two_mul, Real.cos_sq']
  rw [smul_sub, one_smul]
  module

/-! ### Gimbal lock for ZYX (yaw-pitch-roll) Euler angles -/

noncomputable def Rx (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos t, -Real.sin t; 0, Real.sin t, Real.cos t]
noncomputable def Ry (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos t, 0, Real.sin t; 0, 1, 0; -Real.sin t, 0, Real.cos t]
noncomputable def Rz (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos t, -Real.sin t, 0; Real.sin t, Real.cos t, 0; 0, 0, 1]

/-- ZYX Euler map `(yaw ψ, pitch θ, roll φ) ↦ Rz ψ Ry θ Rx φ`. -/
noncomputable def eulerZYX (ψ θ φ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Rz ψ * Ry θ * Rx φ

theorem eulerZYX_pos (ψ φ : ℝ) :
    eulerZYX ψ (Real.pi / 2) φ =
      !![0, Real.sin (φ - ψ), Real.cos (φ - ψ); 0, Real.cos (φ - ψ), -Real.sin (φ - ψ); -1, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [eulerZYX, Rx, Ry, Rz, Matrix.mul_apply, Fin.sum_univ_three, Real.sin_sub,
      Real.cos_sub] <;> ring

theorem eulerZYX_neg (ψ φ : ℝ) :
    eulerZYX ψ (-(Real.pi / 2)) φ =
      !![0, -Real.sin (ψ + φ), -Real.cos (ψ + φ); 0, Real.cos (ψ + φ), -Real.sin (ψ + φ); 1, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [eulerZYX, Rx, Ry, Rz, Matrix.mul_apply, Fin.sum_univ_three, Real.sin_add,
      Real.cos_add] <;> ring

/-- At pitch `+π/2` only `φ - ψ` matters. -/
theorem eulerZYX_gimbal_pos (ψ φ a : ℝ) :
    eulerZYX (ψ + a) (Real.pi / 2) (φ + a) = eulerZYX ψ (Real.pi / 2) φ := by
  rw [eulerZYX_pos, eulerZYX_pos, show φ + a - (ψ + a) = φ - ψ by ring]

/-- At pitch `-π/2` only `ψ + φ` matters. -/
theorem eulerZYX_gimbal_neg (ψ φ a : ℝ) :
    eulerZYX (ψ + a) (-(Real.pi / 2)) (φ - a) = eulerZYX ψ (-(Real.pi / 2)) φ := by
  rw [eulerZYX_neg, eulerZYX_neg, show ψ + a + (φ - a) = ψ + φ by ring]

/-- Euler map is not injective even on `(-π, π]³`. -/
theorem eulerZYX_not_injective :
    eulerZYX 0 (Real.pi / 2) 0 = eulerZYX (Real.pi / 2) (Real.pi / 2) (Real.pi / 2) := by
  have := eulerZYX_gimbal_pos 0 0 (Real.pi / 2)
  rw [zero_add] at this
  exact this.symm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
/-- Singular differential: the Euler map has zero derivative in direction `(1, 0, 1)` at
pitch `π/2`, so its Jacobian has nontrivial kernel. -/
theorem eulerZYX_deriv_kernel (ψ φ : ℝ) :
    HasDerivAt (fun a => eulerZYX (ψ + a) (Real.pi / 2) (φ + a)) 0 0 := by
  have : (fun a => eulerZYX (ψ + a) (Real.pi / 2) (φ + a)) = fun _ => eulerZYX ψ (Real.pi / 2) φ :=
    funext fun a => eulerZYX_gimbal_pos ψ φ a
  rw [this]
  exact hasDerivAt_const (0 : ℝ) (eulerZYX ψ (Real.pi / 2) φ)

end RoboticsLieScratch
