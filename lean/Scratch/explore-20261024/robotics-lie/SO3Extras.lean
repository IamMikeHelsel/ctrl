import ControlsLean.Robotics.SE3Kinematics
import Mathlib

open Matrix ControlsLean.Vision ControlsLean.Robotics

namespace RoboticsLieScratch

/-- General determinant of `I + a K + b K²`, `K = [ω]×`: eigenvalues of `K` are `0, ±i‖ω‖`. -/
theorem det_one_add_skew_poly (ω : Fin 3 → ℝ) (a b : ℝ) :
    (1 + a • skew ω + b • (skew ω * skew ω)).det
      = (1 - b * (ω ⬝ᵥ ω)) ^ 2 + a ^ 2 * (ω ⬝ᵥ ω) := by
  simp [det_fin_three, skew, Fin.sum_univ_three, dotProduct]
  ring

/-- Q: is det R = 1 for Rodrigues with a unit axis? Yes. -/
theorem det_rodrigues (ω : Fin 3 → ℝ) (hω : ω ⬝ᵥ ω = 1) (θ : ℝ) :
    (rodrigues ω θ).det = 1 := by
  rw [rodrigues, det_one_add_skew_poly, hω]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rodrigues_mem_SO3 (ω : Fin 3 → ℝ) (hω : ω ⬝ᵥ ω = 1) (θ : ℝ) :
    rodrigues ω θ ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, det_rodrigues ω hω θ⟩
  rw [mem_orthogonalGroup_iff]
  have := rodrigues_mul_transpose_self ω hω θ
  simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this

/-- Non-unit axis: Rodrigues is NOT orthogonal (ω = 2 e₂, θ = π/2): det = (1-4)² + 4 = 13. -/
theorem det_rodrigues_nonunit :
    (rodrigues ![0, 0, 2] (Real.pi / 2)).det = 13 := by
  rw [rodrigues, det_one_add_skew_poly]
  simp [dotProduct, Fin.sum_univ_three]
  norm_num

/-- Cofactor identity `(M a) × (M b) = adj(M)ᵀ (a × b)`. -/
theorem cross_mulVec' (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    (M *ᵥ a) ⨯₃ (M *ᵥ b) = (adjugate M)ᵀ *ᵥ (a ⨯₃ b) := by
  ext i; fin_cases i <;>
    simp [cross_apply, mulVec, dotProduct, Fin.sum_univ_three, adjugate_fin_three] <;> ring

theorem adjugate_of_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) : adjugate R = Rᵀ := by
  obtain ⟨hO, hdet⟩ := mem_specialOrthogonalGroup_iff.mp hR
  have h1 : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hO
  calc adjugate R = Rᵀ * R * adjugate R := by rw [h1, Matrix.one_mul]
    _ = Rᵀ := by rw [Matrix.mul_assoc, mul_adjugate, hdet, one_smul, Matrix.mul_one]

/-- The equivariance hypothesis `hequiv` of `adjoint6_mul` holds on SO(3). -/
theorem skew_mulVec_mul_of_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    skew (R *ᵥ v) * R = R * skew v := by
  rw [ext_iff_mulVec]
  intro w
  rw [← mulVec_mulVec, ← mulVec_mulVec, skew_mulVec, skew_mulVec, cross_mulVec',
    adjugate_of_SO3 hR, transpose_transpose]

/-- Adjoint for SO(3): `R [v]× Rᵀ = [R v]×`. -/
theorem conj_skew_of_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    R * skew v * Rᵀ = skew (R *ᵥ v) := by
  have h1 : R * Rᵀ = 1 :=
    (mem_orthogonalGroup_iff (Fin 3) ℝ).mp (mem_specialOrthogonalGroup_iff.mp hR).1
  rw [← skew_mulVec_mul_of_SO3 hR, Matrix.mul_assoc, h1, Matrix.mul_one]

/-- Hypothesis-free SE(3) adjoint homomorphism on SO(3). -/
theorem adjoint6_mul_SO3 {R₁ : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R₁ ∈ specialOrthogonalGroup (Fin 3) ℝ) (R₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (p₁ p₂ : Fin 3 → ℝ) :
    adjoint6 (R₁ * R₂) (p₁ + R₁ *ᵥ p₂) = adjoint6 R₁ p₁ * adjoint6 R₂ p₂ :=
  adjoint6_mul R₁ R₂ p₁ p₂ (skew_mulVec_mul_of_SO3 hR p₂)

theorem adjoint6_inv_mul_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) (p : Fin 3 → ℝ) :
    adjoint6 Rᵀ (-(Rᵀ *ᵥ p)) * adjoint6 R p = 1 := by
  have hO := (mem_specialOrthogonalGroup_iff.mp hR).1
  have hRt : Rᵀ ∈ specialOrthogonalGroup (Fin 3) ℝ := by
    rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff, det_transpose]
    refine ⟨?_, (mem_specialOrthogonalGroup_iff.mp hR).2⟩
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hO
  exact adjoint6_inv_mul R p ((mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hO)
    (skew_mulVec_mul_of_SO3 hRt p)

/-- The `hequiv` hypothesis genuinely FAILS on O(3) \ SO(3): with `R = -I`,
`skew (R v) * R = skew v` but `R * skew v = - skew v`. -/
theorem hequiv_fails_reflection :
    ¬ (skew ((-1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![1, 0, 0]) * (-1)
        = (-1) * skew ![1, 0, 0]) := by
  intro h
  have := congrFun (congrFun h 2) 1
  simp [skew, mulVec, dotProduct, Fin.sum_univ_three] at this
  norm_num at this

/-- In general `Rᵀ [R v]× R = det R • [v]×` for orthogonal R. -/
theorem conj_skew_orthogonal {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ orthogonalGroup (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    Rᵀ * skew (R *ᵥ v) * R = R.det • skew v := by
  have h1 : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hR
  have hadj : adjugate R = R.det • Rᵀ := by
    calc adjugate R = Rᵀ * R * adjugate R := by rw [h1, Matrix.one_mul]
      _ = R.det • Rᵀ := by rw [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  rw [ext_iff_mulVec]
  intro w
  rw [← mulVec_mulVec, ← mulVec_mulVec, skew_mulVec, cross_mulVec', hadj, transpose_smul,
    transpose_transpose, mulVec_mulVec, Matrix.mul_smul, h1, smul_mulVec, smul_mulVec,
    one_mulVec, skew_mulVec]

/-- Trace recovers the angle on `[0, π]`. -/
theorem angle_of_trace (ω : Fin 3 → ℝ) (hω : ω ⬝ᵥ ω = 1) {θ : ℝ}
    (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    Real.arccos (((rodrigues ω θ).trace - 1) / 2) = θ := by
  rw [trace_rodrigues ω hω]
  rw [show (1 + 2 * Real.cos θ - 1) / 2 = Real.cos θ by ring]
  exact Real.arccos_cos h0 hπ

/-- Vee / log: the skew part of R is `2 sin θ [ω]×` (no unit hypothesis needed). -/
theorem rodrigues_sub_transpose (ω : Fin 3 → ℝ) (θ : ℝ) :
    rodrigues ω θ - (rodrigues ω θ)ᵀ = (2 * Real.sin θ) • skew ω := by
  rw [rodrigues_transpose]
  simp only [rodrigues, Real.sin_neg, Real.cos_neg, neg_smul]
  rw [two_mul, add_smul]
  abel

/-- Every unit axis has angle-π rotation `R = 2ωωᵀ - I`, symmetric (log ambiguity at π). -/
theorem rodrigues_pi (ω : Fin 3 → ℝ) (hω : ω ⬝ᵥ ω = 1) :
    rodrigues ω Real.pi = 2 • vecMulVec ω ω - 1 := by
  rw [rodrigues, skew_sq, hω]
  simp only [Real.sin_pi, Real.cos_pi, zero_smul, add_zero, one_smul]
  module

/-- `R(ω, θ) = R(-ω, -θ)`: axis-angle is not unique. -/
theorem rodrigues_neg_neg (ω : Fin 3 → ℝ) (θ : ℝ) :
    rodrigues (-ω) (-θ) = rodrigues ω θ := by
  simp [rodrigues, skew_neg, Real.sin_neg, Real.cos_neg]

end RoboticsLieScratch
