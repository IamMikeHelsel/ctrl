import Mathlib

/-! # When Aizerman's intuition *is* a theorem (any dimension)

If one quadratic form `V(x) = xᵀ P x` certifies decay for both endpoint loops
`A + k₁ b cᵀ` and `A + k₂ b cᵀ`, then it certifies decay for every sector-
`[k₁,k₂]` nonlinearity: the Lur'e vector field is pointwise a linear loop with
some gain in `[k₁,k₂]`, and `V̇` is affine in that gain.

Aizerman's conjecture fails exactly when the Hurwitz segment admits no such
common certificate (Pliss 1958, n = 3; Fitts 1966 for Kalman, n = 4). -/

namespace ClassicsFalse

open Matrix

def InSector (k₁ k₂ : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ y, k₁ * y ^ 2 ≤ φ y * y ∧ φ y * y ≤ k₂ * y ^ 2

theorem affine_le_of_endpoints {α β k₁ k₂ k M : ℝ} (hk1 : k₁ ≤ k) (hk2 : k ≤ k₂)
    (h1 : α + β * k₁ ≤ M) (h2 : α + β * k₂ ≤ M) : α + β * k ≤ M := by
  rcases le_total 0 β with hb | hb <;> nlinarith

variable {n : ℕ}

theorem closedLoop_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (b c : Fin n → ℝ) (k : ℝ)
    (x : Fin n → ℝ) :
    (A + k • vecMulVec b c) *ᵥ x = A *ᵥ x + (k * (c ⬝ᵥ x)) • b := by
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

/-- **Common quadratic Lyapunov function at the endpoints ⇒ absolute stability
certificate for the whole sector** (pointwise `V̇ ≤ -ε‖x‖²`). -/
theorem common_lyapunov_sector (A P : Matrix (Fin n) (Fin n) ℝ) (b c : Fin n → ℝ)
    {k₁ k₂ ε : ℝ} {φ : ℝ → ℝ} (hφ : InSector k₁ k₂ φ) (hφ0 : φ 0 = 0)
    (h1 : ∀ x, x ⬝ᵥ (P *ᵥ ((A + k₁ • vecMulVec b c) *ᵥ x)) ≤ -ε * (x ⬝ᵥ x))
    (h2 : ∀ x, x ⬝ᵥ (P *ᵥ ((A + k₂ • vecMulVec b c) *ᵥ x)) ≤ -ε * (x ⬝ᵥ x))
    (x : Fin n → ℝ) :
    x ⬝ᵥ (P *ᵥ (A *ᵥ x + φ (c ⬝ᵥ x) • b)) ≤ -ε * (x ⬝ᵥ x) := by
  set y := c ⬝ᵥ x
  have hlin : ∀ k, x ⬝ᵥ (P *ᵥ ((A + k • vecMulVec b c) *ᵥ x))
      = x ⬝ᵥ (P *ᵥ (A *ᵥ x)) + (y * (x ⬝ᵥ (P *ᵥ b))) * k := by
    intro k
    rw [closedLoop_mulVec, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul]; ring
  have hgoal : x ⬝ᵥ (P *ᵥ (A *ᵥ x + φ y • b))
      = x ⬝ᵥ (P *ᵥ (A *ᵥ x)) + φ y * (x ⬝ᵥ (P *ᵥ b)) := by
    rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hgoal]
  by_cases hy : y = 0
  · have e1 := h1 x; rw [hlin, hy] at e1; rw [hy, hφ0]; simpa using e1
  · have g1 := (hφ y).1; have g2 := (hφ y).2
    set k := φ y / y
    have hk : φ y = y * k := by simp only [k]; field_simp
    have hk1 : k₁ ≤ k := by
      rcases lt_or_gt_of_ne hy with hn | hp
      · rw [le_div_iff_of_neg hn]; nlinarith
      · rw [le_div_iff₀ hp]; nlinarith
    have hk2 : k ≤ k₂ := by
      rcases lt_or_gt_of_ne hy with hn | hp
      · rw [div_le_iff_of_neg hn]; nlinarith
      · rw [div_le_iff₀ hp]; nlinarith
    have := affine_le_of_endpoints (M := -ε * (x ⬝ᵥ x)) hk1 hk2
      (by have := h1 x; rwa [hlin] at this) (by have := h2 x; rwa [hlin] at this)
    rw [hk]; linarith

end ClassicsFalse

#print axioms ClassicsFalse.common_lyapunov_sector
