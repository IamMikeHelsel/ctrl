import Mathlib

/-!
Forward Euler inherits the continuous Lyapunov certificate for small steps:
if `AᵀP + PA = -Q`, `xᵀQx ≥ c‖x‖²` and `xᵀAᵀPAx ≤ C‖x‖²`, then for `0 < h` with `h C < c`,
`(I + hA)ᵀ P (I + hA) - P` is negative definite.
-/

open Matrix

namespace SampledExplore

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma euler_lyap_identity (A P Q : Matrix n n ℝ) (hlyap : Aᵀ * P + P * A = -Q) (h : ℝ) :
    (1 + h • A)ᵀ * P * (1 + h • A) - P = -(h • Q) + (h ^ 2) • (Aᵀ * P * A) := by
  rw [transpose_add, transpose_one, transpose_smul]
  have : -(h • Q) = h • (Aᵀ * P + P * A) := by rw [hlyap, smul_neg]
  rw [this]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_smul, sq]
  abel

theorem forwardEuler_discreteLyapunov {A P Q : Matrix n n ℝ}
    (hlyap : Aᵀ * P + P * A = -Q) {c C : ℝ}
    (hQ : ∀ x : n → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Q *ᵥ x))
    (hR : ∀ x : n → ℝ, x ⬝ᵥ ((Aᵀ * P * A) *ᵥ x) ≤ C * ‖x‖ ^ 2)
    {h : ℝ} (hh : 0 < h) (hhC : h * C < c) (x : n → ℝ) (hx : x ≠ 0) :
    x ⬝ᵥ (((1 + h • A)ᵀ * P * (1 + h • A) - P) *ᵥ x) < 0 := by
  rw [euler_lyap_identity A P Q hlyap h, add_mulVec, neg_mulVec, smul_mulVec, smul_mulVec,
    dotProduct_add, dotProduct_neg, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have h1 := hQ x
  have h2 := hR x
  have : h ^ 2 * (x ⬝ᵥ ((Aᵀ * P * A) *ᵥ x)) ≤ h * (h * C) * ‖x‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg h); nlinarith
  have : h * (h * C) * ‖x‖ ^ 2 < h * c * ‖x‖ ^ 2 := by
    have := mul_lt_mul_of_pos_left hhC hh
    exact mul_lt_mul_of_pos_right this hx2
  nlinarith

end SampledExplore

#print axioms SampledExplore.forwardEuler_discreteLyapunov
