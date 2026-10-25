import Mathlib

/-!
# Dubins (1957): setup and tangent-segment facts

Dubins car: `ẋ = v cos θ, ẏ = v sin θ, θ̇ = ω`, `|ω| ≤ ω_max`. Shortest paths are CSC or CCC.

* `min_turning_radius`: any constant-turn arc has radius `|v/ω| ≥ |v|/ω_max`, with equality at
  `|ω| = ω_max` (the turning circle of radius `r = v/ω_max`).
* CSC tangent segments between two turning circles of radius `r`, centres `c₁, c₂`, `d = ‖c₂-c₁‖`:
  - `outer_tangent_length` (LSL/RSR): length is `d`;
  - `inner_tangent_length` (LSR/RSL): length² is `d² - 4r²`, hence `inner_tangent_needs` `2r ≤ d`;
  - `exists_inner_tangent`: conversely when `2r ≤ d` such a segment exists.
-/

namespace Classics.Dubins

open Real

theorem min_turning_radius {v ω ωmax : ℝ} (hω : ω ≠ 0) (hle : |ω| ≤ ωmax) :
    |v| / ωmax ≤ |v / ω| := by
  rw [abs_div]
  exact div_le_div_of_nonneg_left (abs_nonneg v) (abs_pos.2 hω) hle

theorem turning_radius_eq {v ω ωmax : ℝ} (h : |ω| = ωmax) : |v / ω| = |v| / ωmax := by
  rw [abs_div, h]

/-- Outer tangent (LSL / RSR): tangent points on the same side, `q₂ - c₂ = q₁ - c₁`. -/
theorem outer_tangent_length (c₁ c₂ q₁ q₂ : ℂ) (hside : q₂ - c₂ = q₁ - c₁) :
    ‖q₂ - q₁‖ = ‖c₂ - c₁‖ := by
  congr 1; linear_combination hside

/-- Inner tangent (LSR / RSL): opposite sides, `q₂ - c₂ = -(q₁ - c₁)`, with the segment
orthogonal to the radius at `q₁` and `‖q₁ - c₁‖ = r`. Then `‖q₂ - q₁‖² = d² - 4 r²`. -/
theorem inner_tangent_length (c₁ c₂ q₁ q₂ : ℂ) {r : ℝ} (hr : ‖q₁ - c₁‖ = r)
    (hside : q₂ - c₂ = -(q₁ - c₁)) (hperp : inner ℝ (q₂ - q₁) (q₁ - c₁) = 0) :
    ‖q₂ - q₁‖ ^ 2 = ‖c₂ - c₁‖ ^ 2 - 4 * r ^ 2 := by
  have hc : c₂ - c₁ = (q₂ - q₁) + (2 : ℝ) • (q₁ - c₁) := by
    rw [Complex.real_smul]; push_cast; linear_combination -hside
  have h0 : inner ℝ (q₂ - q₁) ((2 : ℝ) • (q₁ - c₁)) = 0 := by
    rw [inner_smul_right, hperp, mul_zero]
  rw [hc, norm_add_sq_real, h0, norm_smul, hr]
  norm_num; ring

theorem inner_tangent_needs (c₁ c₂ q₁ q₂ : ℂ) {r : ℝ} (hr : ‖q₁ - c₁‖ = r)
    (hside : q₂ - c₂ = -(q₁ - c₁)) (hperp : inner ℝ (q₂ - q₁) (q₁ - c₁) = 0) :
    2 * r ≤ ‖c₂ - c₁‖ := by
  have h := inner_tangent_length c₁ c₂ q₁ q₂ hr hside hperp
  nlinarith [sq_nonneg ‖q₂ - q₁‖, norm_nonneg (c₂ - c₁)]

/-- Existence of the inner (cross) tangent when the turning circles don't overlap. -/
theorem exists_inner_tangent (c₁ c₂ : ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hd : 2 * r ≤ ‖c₂ - c₁‖) :
    ∃ q₁ q₂ : ℂ, ‖q₁ - c₁‖ = r ∧ q₂ - c₂ = -(q₁ - c₁) ∧ inner ℝ (q₂ - q₁) (q₁ - c₁) = 0 := by
  set D := c₂ - c₁ with hD
  set d := ‖D‖
  rcases eq_or_lt_of_le (norm_nonneg D) with h0 | hpos
  · have hr : r = 0 := by linarith [show d = 0 from h0.symm]
    have hD0 : D = 0 := norm_eq_zero.1 h0.symm
    refine ⟨c₁, c₁, by simp [hr], ?_, by simp⟩
    have : c₂ = c₁ := by linear_combination hD0
    simp [this]
  · have hd0 : d ≠ 0 := hpos.ne'
    obtain ⟨k, hk_def⟩ : ∃ k, k = 2 * r / d := ⟨_, rfl⟩
    obtain ⟨e, he_def⟩ : ∃ e, e = r / d := ⟨_, rfl⟩
    have hk : k * d = 2 * r := by rw [hk_def]; field_simp
    have he : e * d = r := by rw [he_def]; field_simp
    set s := √(1 - k ^ 2)
    have hk1 : k ^ 2 ≤ 1 := by
      rw [hk_def, div_pow, div_le_one (by positivity)]
      exact pow_le_pow_left₀ (by positivity) hd 2
    have hks : k ^ 2 + s ^ 2 = 1 := by rw [sq_sqrt (by linarith)]; ring
    have hd2 : d ^ 2 = D.re ^ 2 + D.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    set u : ℂ := (e : ℂ) * ((k : ℂ) * D + (s : ℂ) * Complex.I * D) with hu
    have hure : u.re = e * (k * D.re - s * D.im) := by simp [u]; ring_nf; simp
    have huim : u.im = e * (k * D.im + s * D.re) := by simp [u]
    have hnu : ‖u‖ ^ 2 = r ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hure, huim]
      linear_combination e ^ 2 * (D.re ^ 2 + D.im ^ 2) * hks - e ^ 2 * hd2 + (e * d + r) * he
    refine ⟨c₁ + u, c₂ - u, ?_, by ring, ?_⟩
    · rw [add_sub_cancel_left]
      exact (pow_left_inj₀ (norm_nonneg _) hr0 two_ne_zero).1 hnu
    · rw [show c₂ - u - (c₁ + u) = D - 2 * u by rw [hD]; ring, add_sub_cancel_left,
        Complex.inner]
      have : (u * (starRingEnd ℂ) (D - 2 * u)).re = (u * (starRingEnd ℂ) D).re - 2 * ‖u‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      rw [this, hnu]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hure, huim]
      linear_combination -e * k * hd2 + k * d * he + r * hk

end Classics.Dubins
