import Mathlib

/-!
# Kalman–Yakubovich–Popov lemma, one-state version

System `ẋ = -a x + u`, `y = c x + d u` with `a > 0`, so `G(s) = c/(s + a) + d` and
`Re G(iω) = c a / (a² + ω²) + d`. KYP (positive-real form): with storage `V = P x² / 2`,
the dissipation LMI `[[-2aP, P - c], [P - c, -2d]] ≤ 0` reduces (given `a, P > 0`) to
`(P - c)² ≤ 4 a d P`.

`scalar_kyp`: for `c ≠ 0` (minimality), `G` is positive real iff the LMI has a solution `P > 0`.
-/

namespace ClassicsFrequency

/-- Frequency-domain side: closed form of positive realness. -/
theorem pr_iff {a c d : ℝ} (ha : 0 < a) :
    (∀ ω : ℝ, 0 ≤ c * a / (a ^ 2 + ω ^ 2) + d) ↔ 0 ≤ d ∧ 0 ≤ c + a * d := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hd
      push Not at hd
      -- large ω: c a / (a² + ω²) → 0
      set ω := √((|c| * a + 1) / (-d)) with hω
      have hdpos : 0 < -d := by linarith
      have hω2 : ω ^ 2 = (|c| * a + 1) / (-d) := Real.sq_sqrt (by positivity)
      have h1 := h ω
      have hden : 0 < a ^ 2 + ω ^ 2 := by positivity
      rw [div_add' _ _ _ hden.ne', le_div_iff₀ hden, zero_mul] at h1
      rw [hω2] at h1
      have : (-d) * ((|c| * a + 1) / (-d)) = |c| * a + 1 := mul_div_cancel₀ _ hdpos.ne'
      have e1 : c * a ≤ |c| * a := mul_le_mul_of_nonneg_right (le_abs_self c) ha.le
      have e2 : d * a ^ 2 < 0 := mul_neg_of_neg_of_pos hd (by positivity)
      linarith
    · have h0 := h 0
      have : c * a / (a ^ 2 + 0 ^ 2) = c / a := by
        rw [zero_pow two_ne_zero, add_zero]; field_simp
      rw [this] at h0
      have := mul_nonneg ha.le h0
      rw [mul_add, mul_div_cancel₀ _ ha.ne'] at this
      linarith
  · rintro ⟨hd, hcd⟩ ω
    have hden : 0 < a ^ 2 + ω ^ 2 := by positivity
    rw [div_add' _ _ _ hden.ne', le_div_iff₀ hden, zero_mul]
    nlinarith [sq_nonneg ω, mul_nonneg hd (sq_nonneg ω)]

/-- **Scalar KYP lemma.** -/
theorem scalar_kyp {a c d : ℝ} (ha : 0 < a) (hc : c ≠ 0) :
    (∀ ω : ℝ, 0 ≤ c * a / (a ^ 2 + ω ^ 2) + d) ↔ ∃ P > 0, (P - c) ^ 2 ≤ 4 * a * d * P := by
  rw [pr_iff ha]
  constructor
  · rintro ⟨hd, hcd⟩
    refine ⟨c + 2 * a * d, ?_, ?_⟩
    · rcases hd.lt_or_eq with hd | hd
      · nlinarith [mul_pos ha hd]
      · subst hd
        simp at hcd ⊢
        exact lt_of_le_of_ne hcd (Ne.symm hc)
    · nlinarith [mul_nonneg (mul_nonneg ha.le hd) hcd]
  · rintro ⟨P, hP, hLMI⟩
    have hd : 0 ≤ d := by
      by_contra h
      push Not at h
      nlinarith [sq_nonneg (P - c), mul_pos ha hP]
    refine ⟨hd, ?_⟩
    rcases hd.lt_or_eq with hd' | hd'
    · by_contra h
      push Not at h
      -- (P - c)² ≤ 4adP  ⇒ (P - (c + 2ad))² ≤ 4ad(c + ad) < 0
      nlinarith [sq_nonneg (P - (c + 2 * a * d)), mul_pos ha hd']
    · subst hd'
      have : P = c := by nlinarith [sq_nonneg (P - c)]
      simp; linarith

end ClassicsFrequency
