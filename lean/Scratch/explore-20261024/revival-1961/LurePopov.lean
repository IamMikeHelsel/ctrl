import Mathlib

/-!
# Lur'e–Postnikov / Popov (1944/1961) on a saturated steering loop

Popov (1961) and the Lur'e–Postnikov Lyapunov function
`V(x) = xᵀPx + 2η ∫₀^{cᵀx} φ(s) ds`
certify *absolute stability*: stability for every memoryless nonlinearity in a sector.

Modern instance: a first-order-lag steering actuator driving a self-aligning lateral error,
with an arbitrary memoryless steering map `φ` (torque clamp, deadzone, smooth saturation …):

  `ẋ₁ = −x₁ + x₂`   (lateral/heading error, self-aligning, driven by actuator state)
  `ẋ₂ = −x₂ − φ(x₁)` (actuator lag, commanded by the nonlinear feedback)

With `V = x₁² + x₂² + 2∫₀^{x₁} φ` we get `V̇ ≤ −(x₁² + x₂²)` for **every** `φ` with
`σ φ(σ) ≥ 0` (infinite sector), and `V̇ ≤ −V/(1+k)` (exponential rate) when `φ ∈ [0, k]`.
-/

namespace Revival1961

open intervalIntegral MeasureTheory Set

/-- The Lur'e integral term `Φ(σ) = ∫₀^σ φ`. -/
noncomputable def Phi (φ : ℝ → ℝ) (σ : ℝ) : ℝ := ∫ s in (0 : ℝ)..σ, φ s

/-- Sector `[0, ∞)`: first/third quadrant nonlinearity. -/
def Sector0 (φ : ℝ → ℝ) : Prop := ∀ s, 0 ≤ s * φ s

/-- Sector `[0, k]`. -/
def SectorK (φ : ℝ → ℝ) (k : ℝ) : Prop := ∀ s, 0 ≤ s * φ s ∧ s * φ s ≤ k * s ^ 2

lemma Phi_hasDerivAt {φ : ℝ → ℝ} (hφ : Continuous φ) (σ : ℝ) :
    HasDerivAt (Phi φ) (φ σ) σ :=
  (hφ.integral_hasStrictDerivAt 0 σ).hasDerivAt

lemma sector_pos {φ : ℝ → ℝ} (h : Sector0 φ) {u : ℝ} (hu : 0 < u) : 0 ≤ φ u := by
  have := h u; nlinarith

lemma sector_neg {φ : ℝ → ℝ} (h : Sector0 φ) {u : ℝ} (hu : u < 0) : φ u ≤ 0 := by
  have := h u; nlinarith

/-- `Φ ≥ 0` in the sector (so `V` dominates the quadratic part). -/
theorem Phi_nonneg {φ : ℝ → ℝ} (hφ : Continuous φ) (hφ0 : φ 0 = 0) (h : Sector0 φ) (σ : ℝ) :
    0 ≤ Phi φ σ := by
  unfold Phi
  rcases le_or_gt 0 σ with hσ | hσ
  · refine integral_nonneg hσ fun u hu => ?_
    rcases hu.1.eq_or_lt with h0 | h0
    · rw [← h0, hφ0]
    · exact sector_pos h h0
  · rw [integral_symm, neg_nonneg]
    have := integral_mono_on (μ := volume) hσ.le (hφ.intervalIntegrable σ 0)
      (continuous_const.intervalIntegrable (μ := volume) σ 0) (g := fun _ => (0 : ℝ))
      (fun u hu => by
        rcases hu.2.eq_or_lt with h0 | h0
        · rw [h0, hφ0]
        · exact sector_neg h h0)
    simpa using this

/-- In sector `[0,k]`, `Φ(σ) ≤ k σ² / 2`. -/
theorem Phi_le {φ : ℝ → ℝ} {k : ℝ} (hφ : Continuous φ) (hφ0 : φ 0 = 0) (h : SectorK φ k)
    (σ : ℝ) : Phi φ σ ≤ k * σ ^ 2 / 2 := by
  unfold Phi
  have hlin : Continuous fun u : ℝ => k * u := continuous_const.mul continuous_id
  have hint : ∀ a b : ℝ, ∫ u in a..b, k * u = k * ((b ^ 2 - a ^ 2) / 2) := fun a b => by
    rw [intervalIntegral.integral_const_mul, integral_id]
  rcases le_or_gt 0 σ with hσ | hσ
  · have := integral_mono_on (μ := volume) hσ (hφ.intervalIntegrable 0 σ)
      (hlin.intervalIntegrable 0 σ) (fun u hu => by
        rcases hu.1.eq_or_lt with h0 | h0
        · rw [← h0, hφ0]; simp
        · have := (h u).2; nlinarith)
    rw [hint] at this; linarith
  · rw [integral_symm]
    have := integral_mono_on (μ := volume) hσ.le (hlin.intervalIntegrable σ 0)
      (hφ.intervalIntegrable σ 0) (fun u hu => by
        rcases hu.2.eq_or_lt with h0 | h0
        · rw [h0, hφ0]; simp
        · have := (h u).2; nlinarith)
    rw [hint] at this; linarith

/-- The Lur'e–Postnikov function for the steering loop. -/
noncomputable def Vlure (φ : ℝ → ℝ) (x₁ x₂ : ℝ) : ℝ := x₁ ^ 2 + x₂ ^ 2 + 2 * Phi φ x₁

/-- **Absolute stability certificate (infinite sector).** Along any trajectory of the
saturated steering loop, `V` has derivative `≤ −(x₁² + x₂²)` for every continuous `φ` with
`σ φ(σ) ≥ 0`. -/
theorem lure_steering_decrease {φ : ℝ → ℝ} (hφ : Continuous φ) (hsec : Sector0 φ)
    {x₁ x₂ : ℝ → ℝ} {t : ℝ}
    (h₁ : HasDerivAt x₁ (-x₁ t + x₂ t) t) (h₂ : HasDerivAt x₂ (-x₂ t - φ (x₁ t)) t) :
    ∃ d, HasDerivAt (fun s => Vlure φ (x₁ s) (x₂ s)) d t ∧ d ≤ -(x₁ t ^ 2 + x₂ t ^ 2) := by
  have hΦ := (Phi_hasDerivAt hφ (x₁ t)).comp t h₁
  refine ⟨_, ((h₁.pow 2).add (h₂.pow 2)).add (hΦ.const_mul 2), ?_⟩
  have := hsec (x₁ t)
  norm_num
  nlinarith [sq_nonneg (x₁ t - x₂ t)]

/-- **Exponential rate in sector `[0,k]`**: `V̇ ≤ −V/(1+k)`, and `V ≥ x₁² + x₂²`. -/
theorem lure_steering_exponential {φ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hφ : Continuous φ)
    (hφ0 : φ 0 = 0) (hsec : SectorK φ k) {x₁ x₂ : ℝ → ℝ} {t : ℝ}
    (h₁ : HasDerivAt x₁ (-x₁ t + x₂ t) t) (h₂ : HasDerivAt x₂ (-x₂ t - φ (x₁ t)) t) :
    x₁ t ^ 2 + x₂ t ^ 2 ≤ Vlure φ (x₁ t) (x₂ t) ∧
    ∃ d, HasDerivAt (fun s => Vlure φ (x₁ s) (x₂ s)) d t ∧
      d ≤ -(Vlure φ (x₁ t) (x₂ t)) / (1 + k) := by
  have h0 : Sector0 φ := fun s => (hsec s).1
  have hlo := Phi_nonneg hφ hφ0 h0 (x₁ t)
  have hhi := Phi_le hφ hφ0 hsec (x₁ t)
  refine ⟨by unfold Vlure; linarith, ?_⟩
  obtain ⟨d, hd, hdle⟩ := lure_steering_decrease hφ h0 h₁ h₂
  refine ⟨d, hd, ?_⟩
  have hV : Vlure φ (x₁ t) (x₂ t) ≤ (1 + k) * (x₁ t ^ 2 + x₂ t ^ 2) := by
    unfold Vlure; nlinarith [sq_nonneg (x₂ t), mul_nonneg hk (sq_nonneg (x₂ t))]
  rw [neg_div, le_neg, div_le_iff₀ (by linarith)]
  nlinarith

/-! ### Instantiation: hard steering-torque clamp `sat_U(σ) = max (−U) (min U σ)` -/

/-- Steering torque clamp. -/
def sat (U σ : ℝ) : ℝ := max (-U) (min U σ)

lemma sat_continuous (U : ℝ) : Continuous (sat U) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma sat_zero {U : ℝ} (hU : 0 ≤ U) : sat U 0 = 0 := by
  simp [sat, hU]

/-- The clamp lies in sector `[0, 1]`. -/
lemma sat_sector {U : ℝ} (hU : 0 ≤ U) : SectorK (sat U) 1 := by
  intro s
  unfold sat
  rcases le_total s U with h1 | h1 <;> rcases le_total (-U) s with h2 | h2
  · rw [min_eq_right h1, max_eq_right h2]; constructor <;> nlinarith
  · rw [min_eq_right h1, max_eq_left (by linarith)]; constructor <;> nlinarith
  · rw [min_eq_left h1, max_eq_right (by linarith)]; constructor <;> nlinarith
  · have : s = 0 := by linarith
    subst this; simp

/-- **Saturated steering loop is globally exponentially stable (rate ½ in `V`)**, for every
torque limit `U ≥ 0`. -/
theorem saturated_steering_exponential {U : ℝ} (hU : 0 ≤ U) {x₁ x₂ : ℝ → ℝ} {t : ℝ}
    (h₁ : HasDerivAt x₁ (-x₁ t + x₂ t) t) (h₂ : HasDerivAt x₂ (-x₂ t - sat U (x₁ t)) t) :
    ∃ d, HasDerivAt (fun s => Vlure (sat U) (x₁ s) (x₂ s)) d t ∧
      d ≤ -(Vlure (sat U) (x₁ t) (x₂ t)) / 2 := by
  obtain ⟨-, d, hd, hle⟩ := lure_steering_exponential zero_le_one (sat_continuous U)
    (sat_zero hU) (sat_sector hU) h₁ h₂
  exact ⟨d, hd, by norm_num at hle ⊢; linarith⟩

end Revival1961
