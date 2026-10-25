import Mathlib

/-! Aizerman's conjecture (1949) holds for first-order systems, with an explicit
exponential rate equal to the worst linear rate over the Hurwitz sector. -/

namespace ClassicsFalse

open Real

def InSector (k₁ k₂ : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ y, k₁ * y ^ 2 ≤ φ y * y ∧ φ y * y ≤ k₂ * y ^ 2

/-- Hurwitz sector for `ẋ = a x + b k x`: endpoint stability ⇔ stability on the
whole segment, because the closed-loop pole `a + b k` is affine in `k`. -/
theorem hurwitz_segment_iff {a b k₁ k₂ : ℝ} (hk : k₁ ≤ k₂) :
    (∀ k ∈ Set.Icc k₁ k₂, a + b * k < 0) ↔ (a + b * k₁ < 0 ∧ a + b * k₂ < 0) := by
  constructor
  · intro h; exact ⟨h k₁ ⟨le_rfl, hk⟩, h k₂ ⟨hk, le_rfl⟩⟩
  · rintro ⟨h1, h2⟩ k ⟨hk1, hk2⟩
    rcases le_total 0 b with hb | hb <;> nlinarith

/-- Pointwise Lyapunov inequality for `V = x²`. -/
theorem lyap_pointwise {a b k₁ k₂ : ℝ} {φ : ℝ → ℝ} (hφ : InSector k₁ k₂ φ) (x : ℝ) :
    x * (a * x + b * φ x) ≤ max (a + b * k₁) (a + b * k₂) * x ^ 2 := by
  obtain ⟨h1, h2⟩ := hφ x
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  rcases le_total 0 b with hb | hb
  · have : b * (φ x * x) ≤ b * (k₂ * x ^ 2) := mul_le_mul_of_nonneg_left h2 hb
    nlinarith [mul_le_mul_of_nonneg_right (le_max_right (a + b * k₁) (a + b * k₂)) hx2]
  · have : b * (φ x * x) ≤ b * (k₁ * x ^ 2) := mul_le_mul_of_nonpos_left h1 hb
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left (a + b * k₁) (a + b * k₂)) hx2]

/-- **Aizerman, n = 1.** If every linear gain `k ∈ [k₁,k₂]` gives a stable
scalar loop, then every (not necessarily continuous) sector-`[k₁,k₂]`
nonlinearity gives exponential decay `x(t)² ≤ x(0)² e^{-2μt}` with
`μ = min(-(a+bk₁), -(a+bk₂)) > 0`. -/
theorem aizerman_scalar {a b k₁ k₂ : ℝ} {φ : ℝ → ℝ} (hφ : InSector k₁ k₂ φ)
    (x : ℝ → ℝ) (hx : ∀ t, HasDerivAt x (a * x t + b * φ (x t)) t) {t : ℝ} (ht : 0 ≤ t) :
    x t ^ 2 ≤ x 0 ^ 2 * exp (-(2 * min (-(a + b * k₁)) (-(a + b * k₂))) * t) := by
  set μ := min (-(a + b * k₁)) (-(a + b * k₂)) with hμ
  have hmax : max (a + b * k₁) (a + b * k₂) = -μ := by
    rw [hμ, min_neg_neg, neg_neg]
  let g : ℝ → ℝ := fun s => x s ^ 2 * exp (2 * μ * s)
  have hg : ∀ s, HasDerivAt g
      (2 * x s * (a * x s + b * φ (x s)) * exp (2 * μ * s)
        + x s ^ 2 * (exp (2 * μ * s) * (2 * μ))) s := by
    intro s
    have hx2 := (hx s).pow 2
    have he := ((hasDerivAt_id s).const_mul (2 * μ)).exp
    have := hx2.mul he
    exact this.congr_deriv (by simp only [id_eq, mul_one, Nat.cast_ofNat, Pi.pow_apply]; ring)
  have hanti : Antitone g := by
    apply antitone_of_deriv_nonpos (fun s => (hg s).differentiableAt)
    intro s
    rw [(hg s).deriv]
    have hp := lyap_pointwise (a := a) (b := b) hφ (x s)
    rw [hmax] at hp
    have he := exp_pos (2 * μ * s)
    nlinarith
  have := hanti ht
  simp only [g, mul_zero, exp_zero, mul_one] at this
  have he := exp_pos (2 * μ * t)
  have key : x t ^ 2 = x t ^ 2 * exp (2 * μ * t) * exp (-(2 * μ) * t) := by
    rw [mul_assoc, ← exp_add]; ring_nf; simp
  rw [key]
  exact mul_le_mul_of_nonneg_right this (exp_pos _).le

/-- Consequence: the state converges to `0`. -/
theorem aizerman_scalar_tendsto {a b k₁ k₂ : ℝ} {φ : ℝ → ℝ} (hφ : InSector k₁ k₂ φ)
    (h1 : a + b * k₁ < 0) (h2 : a + b * k₂ < 0)
    (x : ℝ → ℝ) (hx : ∀ t, HasDerivAt x (a * x t + b * φ (x t)) t) :
    Filter.Tendsto (fun t => x t ^ 2) Filter.atTop (nhds 0) := by
  set μ := min (-(a + b * k₁)) (-(a + b * k₂))
  have hμ : 0 < μ := lt_min (by linarith) (by linarith)
  have hlim : Filter.Tendsto (fun t => x 0 ^ 2 * exp (-(2 * μ) * t)) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun t => exp (-(2 * μ) * t)) Filter.atTop (nhds 0) := by
      apply tendsto_exp_atBot.comp
      exact Filter.tendsto_id.const_mul_atTop_of_neg (by linarith)
    simpa using this.const_mul (x 0 ^ 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Filter.Eventually.of_forall fun t => sq_nonneg _
  · filter_upwards [Filter.eventually_ge_atTop 0] with t ht
    exact aizerman_scalar hφ x hx ht

end ClassicsFalse

#print axioms ClassicsFalse.aizerman_scalar_tendsto
