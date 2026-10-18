/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Order.Filter.Basic

/-!
# Discrete-time small-gain theorem

Signals are sequences `ℕ → E` in a seminormed group. Instead of working in `ℓ∞`, we use the
truncated sup norm `‖u‖ₖ = max_{i ≤ k} ‖u i‖` (`truncNorm u k`), which is finite for every
signal. An operator `G` has *finite gain* `γ` with bias `β` if `‖G u‖ₖ ≤ γ ‖u‖ₖ + β` for all
`u` and `k`.

For the feedback interconnection `e₁ = u₁ + G₂ e₂`, `e₂ = u₂ + G₁ e₁` with `γ₁ γ₂ < 1`, any
solution satisfies
`‖e₁‖ₖ ≤ (‖u₁‖ₖ + γ₂ ‖u₂‖ₖ + β₂ + γ₂ β₁) / (1 - γ₁ γ₂)`
and symmetrically for `e₂`. Well-posedness (existence of `e₁, e₂`) is assumed. The negative
feedback convention `e₁ = u₁ - G₂ e₂` is covered by `HasGain.neg`.

Because the gain condition is stated on truncations, causality is not needed for the bound.
We still define `Causal` and show that the truncated norm of a causal operator's output only
depends on the truncated input.

We also show that a linear operator with finite gain has the same gain with zero bias, and that
bounded inputs give bounded closed-loop signals.
-/

open Finset

namespace ControlsLean.Controls

variable {E F : Type*}

section Seminormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- Truncated sup norm `‖u‖ₖ = max_{i ≤ k} ‖u i‖`. -/
noncomputable def truncNorm (u : ℕ → E) (k : ℕ) : ℝ :=
  (range (k + 1)).sup' nonempty_range_add_one fun i => ‖u i‖

/-- `G` has finite gain `γ` with bias `β` with respect to truncated sup norms. -/
def HasGain (G : (ℕ → E) → (ℕ → F)) (γ β : ℝ) : Prop :=
  ∀ u k, truncNorm (G u) k ≤ γ * truncNorm u k + β

/-- `G` is causal: the output up to time `k` depends only on the input up to time `k`. -/
def Causal (G : (ℕ → E) → (ℕ → F)) : Prop :=
  ∀ u v k, (∀ i ≤ k, u i = v i) → ∀ i ≤ k, G u i = G v i

theorem norm_le_truncNorm (u : ℕ → E) {i k : ℕ} (hi : i ≤ k) : ‖u i‖ ≤ truncNorm u k :=
  le_sup' (fun i => ‖u i‖) (mem_range.2 (Nat.lt_succ_of_le hi))

theorem truncNorm_le_iff {u : ℕ → E} {k : ℕ} {M : ℝ} :
    truncNorm u k ≤ M ↔ ∀ i ≤ k, ‖u i‖ ≤ M := by
  simp [truncNorm]

theorem truncNorm_nonneg (u : ℕ → E) (k : ℕ) : 0 ≤ truncNorm u k :=
  (norm_nonneg _).trans (norm_le_truncNorm u le_rfl)

theorem truncNorm_congr {u v : ℕ → E} {k : ℕ} (h : ∀ i ≤ k, ‖u i‖ = ‖v i‖) :
    truncNorm u k = truncNorm v k :=
  sup'_congr _ rfl fun i hi => h i (Nat.lt_succ_iff.1 (mem_range.1 hi))

theorem truncNorm_mono (u : ℕ → E) {j k : ℕ} (h : j ≤ k) : truncNorm u j ≤ truncNorm u k :=
  truncNorm_le_iff.2 fun _ hi => norm_le_truncNorm u (hi.trans h)

theorem truncNorm_add_le (u v : ℕ → E) (k : ℕ) :
    truncNorm (u + v) k ≤ truncNorm u k + truncNorm v k :=
  truncNorm_le_iff.2 fun _ hi =>
    (norm_add_le _ _).trans (add_le_add (norm_le_truncNorm u hi) (norm_le_truncNorm v hi))

@[simp] theorem truncNorm_neg (u : ℕ → E) (k : ℕ) : truncNorm (-u) k = truncNorm u k :=
  truncNorm_congr fun _ _ => norm_neg _

theorem truncNorm_le_of_bounded {u : ℕ → E} {M : ℝ} (h : ∀ i, ‖u i‖ ≤ M) (k : ℕ) :
    truncNorm u k ≤ M :=
  truncNorm_le_iff.2 fun i _ => h i

omit [SeminormedAddCommGroup E] in
/-- The truncated output norm of a causal operator depends only on the truncated input. -/
theorem Causal.truncNorm_eq {G : (ℕ → E) → (ℕ → F)} (hG : Causal G) {u v : ℕ → E} {k : ℕ}
    (h : ∀ i ≤ k, u i = v i) : truncNorm (G u) k = truncNorm (G v) k :=
  truncNorm_congr fun i hi => by rw [hG u v k h i hi]

/-- Negating the output preserves the gain, so `e₁ = u₁ - G₂ e₂` is also covered. -/
theorem HasGain.neg {G : (ℕ → E) → (ℕ → F)} {γ β : ℝ} (hG : HasGain G γ β) :
    HasGain (fun u => -G u) γ β := fun u k => by simpa using hG u k

/-- **Discrete-time small-gain theorem** (bound on `e₁`). If `e₁ = u₁ + G₂ e₂` and
`e₂ = u₂ + G₁ e₁` with `γ₁ γ₂ < 1`, the truncated norm of `e₁` is bounded explicitly in terms
of the truncated norms of the inputs. -/
theorem small_gain_left {G₁ : (ℕ → E) → (ℕ → F)} {G₂ : (ℕ → F) → (ℕ → E)}
    {γ₁ γ₂ β₁ β₂ : ℝ} (hG₁ : HasGain G₁ γ₁ β₁) (hG₂ : HasGain G₂ γ₂ β₂)
    (hγ₂ : 0 ≤ γ₂) (hγ : γ₁ * γ₂ < 1) {u₁ e₁ : ℕ → E} {u₂ e₂ : ℕ → F}
    (h₁ : e₁ = u₁ + G₂ e₂) (h₂ : e₂ = u₂ + G₁ e₁) (k : ℕ) :
    truncNorm e₁ k ≤
      (truncNorm u₁ k + γ₂ * truncNorm u₂ k + β₂ + γ₂ * β₁) / (1 - γ₁ * γ₂) := by
  have hb₁ : truncNorm e₁ k ≤ truncNorm u₁ k + (γ₂ * truncNorm e₂ k + β₂) := by
    rw [h₁]; exact (truncNorm_add_le _ _ k).trans (add_le_add_right (hG₂ e₂ k) _)
  have hb₂ : truncNorm e₂ k ≤ truncNorm u₂ k + (γ₁ * truncNorm e₁ k + β₁) := by
    conv_lhs => rw [h₂]
    exact (truncNorm_add_le _ _ k).trans (add_le_add_right (hG₁ e₁ k) _)
  have := mul_le_mul_of_nonneg_left hb₂ hγ₂
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **Discrete-time small-gain theorem** (bound on `e₂`). -/
theorem small_gain_right {G₁ : (ℕ → E) → (ℕ → F)} {G₂ : (ℕ → F) → (ℕ → E)}
    {γ₁ γ₂ β₁ β₂ : ℝ} (hG₁ : HasGain G₁ γ₁ β₁) (hG₂ : HasGain G₂ γ₂ β₂)
    (hγ₁ : 0 ≤ γ₁) (hγ : γ₁ * γ₂ < 1) {u₁ e₁ : ℕ → E} {u₂ e₂ : ℕ → F}
    (h₁ : e₁ = u₁ + G₂ e₂) (h₂ : e₂ = u₂ + G₁ e₁) (k : ℕ) :
    truncNorm e₂ k ≤
      (truncNorm u₂ k + γ₁ * truncNorm u₁ k + β₁ + γ₁ * β₂) / (1 - γ₁ * γ₂) := by
  rw [mul_comm γ₁ γ₂]
  exact small_gain_left hG₂ hG₁ hγ₁ (by linarith [mul_comm γ₁ γ₂]) h₂ h₁ k

/-- **Small-gain theorem**: both closed-loop signals satisfy explicit truncated-norm bounds. -/
theorem small_gain {G₁ : (ℕ → E) → (ℕ → F)} {G₂ : (ℕ → F) → (ℕ → E)}
    {γ₁ γ₂ β₁ β₂ : ℝ} (hG₁ : HasGain G₁ γ₁ β₁) (hG₂ : HasGain G₂ γ₂ β₂)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂) (hγ : γ₁ * γ₂ < 1) {u₁ e₁ : ℕ → E} {u₂ e₂ : ℕ → F}
    (h₁ : e₁ = u₁ + G₂ e₂) (h₂ : e₂ = u₂ + G₁ e₁) (k : ℕ) :
    truncNorm e₁ k ≤
        (truncNorm u₁ k + γ₂ * truncNorm u₂ k + β₂ + γ₂ * β₁) / (1 - γ₁ * γ₂) ∧
      truncNorm e₂ k ≤
        (truncNorm u₂ k + γ₁ * truncNorm u₁ k + β₁ + γ₁ * β₂) / (1 - γ₁ * γ₂) :=
  ⟨small_gain_left hG₁ hG₂ hγ₂ hγ h₁ h₂ k, small_gain_right hG₁ hG₂ hγ₁ hγ h₁ h₂ k⟩

/-- **Bounded-input bounded-signal**: bounded external inputs give bounded closed-loop
signals, with explicit bounds. -/
theorem small_gain_bounded {G₁ : (ℕ → E) → (ℕ → F)} {G₂ : (ℕ → F) → (ℕ → E)}
    {γ₁ γ₂ β₁ β₂ : ℝ} (hG₁ : HasGain G₁ γ₁ β₁) (hG₂ : HasGain G₂ γ₂ β₂)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂) (hγ : γ₁ * γ₂ < 1) {u₁ e₁ : ℕ → E} {u₂ e₂ : ℕ → F}
    (h₁ : e₁ = u₁ + G₂ e₂) (h₂ : e₂ = u₂ + G₁ e₁) {M₁ M₂ : ℝ}
    (hu₁ : ∀ i, ‖u₁ i‖ ≤ M₁) (hu₂ : ∀ i, ‖u₂ i‖ ≤ M₂) :
    (∀ i, ‖e₁ i‖ ≤ (M₁ + γ₂ * M₂ + β₂ + γ₂ * β₁) / (1 - γ₁ * γ₂)) ∧
      ∀ i, ‖e₂ i‖ ≤ (M₂ + γ₁ * M₁ + β₁ + γ₁ * β₂) / (1 - γ₁ * γ₂) := by
  have hpos : 0 < 1 - γ₁ * γ₂ := by linarith
  refine ⟨fun i => ?_, fun i => ?_⟩
  · refine (norm_le_truncNorm e₁ le_rfl).trans <|
      (small_gain_left hG₁ hG₂ hγ₂ hγ h₁ h₂ i).trans ?_
    gcongr
    · exact truncNorm_le_of_bounded hu₁ i
    · exact truncNorm_le_of_bounded hu₂ i
  · refine (norm_le_truncNorm e₂ le_rfl).trans <|
      (small_gain_right hG₁ hG₂ hγ₁ hγ h₁ h₂ i).trans ?_
    gcongr
    · exact truncNorm_le_of_bounded hu₂ i
    · exact truncNorm_le_of_bounded hu₁ i

end Seminormed

section Linear

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] [SeminormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem truncNorm_smul (c : ℝ) (u : ℕ → E) (k : ℕ) :
    truncNorm (c • u) k = |c| * truncNorm u k := by
  apply le_antisymm
  · exact truncNorm_le_iff.2 fun i hi => by
      simpa [norm_smul] using mul_le_mul_of_nonneg_left (norm_le_truncNorm u hi) (abs_nonneg c)
  · rcases eq_or_ne c 0 with rfl | hc
    · simpa using truncNorm_nonneg _ k
    rw [← le_div_iff₀' (abs_pos.2 hc)]
    exact truncNorm_le_iff.2 fun i hi => by
      rw [le_div_iff₀' (abs_pos.2 hc), ← Real.norm_eq_abs, ← norm_smul]
      exact norm_le_truncNorm (c • u) hi

/-- A linear operator with finite gain `γ` and any bias `β` has gain `γ` with zero bias. -/
theorem HasGain.linear_zero_bias (G : (ℕ → E) →ₗ[ℝ] (ℕ → F)) {γ β : ℝ} (hG : HasGain G γ β) :
    HasGain G γ 0 := by
  intro u k
  rw [add_zero]
  by_contra hlt
  rw [not_le] at hlt
  set d := truncNorm (G u) k - γ * truncNorm u k with hd
  have hd0 : 0 < d := by linarith
  set t := (|β| + 1) / d with ht
  have ht0 : 0 < t := by positivity
  have h := hG (t • u) k
  rw [map_smul, truncNorm_smul, truncNorm_smul, abs_of_pos ht0] at h
  have htd : t * d = |β| + 1 := div_mul_cancel₀ _ hd0.ne'
  nlinarith [le_abs_self β]

/-- **Small-gain theorem for linear operators**: zero-bias bounds for both signals. -/
theorem small_gain_linear (G₁ : (ℕ → E) →ₗ[ℝ] (ℕ → F)) (G₂ : (ℕ → F) →ₗ[ℝ] (ℕ → E))
    {γ₁ γ₂ β₁ β₂ : ℝ} (hG₁ : HasGain G₁ γ₁ β₁) (hG₂ : HasGain G₂ γ₂ β₂)
    (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂) (hγ : γ₁ * γ₂ < 1) {u₁ e₁ : ℕ → E} {u₂ e₂ : ℕ → F}
    (h₁ : e₁ = u₁ + G₂ e₂) (h₂ : e₂ = u₂ + G₁ e₁) (k : ℕ) :
    truncNorm e₁ k ≤ (truncNorm u₁ k + γ₂ * truncNorm u₂ k) / (1 - γ₁ * γ₂) ∧
      truncNorm e₂ k ≤ (truncNorm u₂ k + γ₁ * truncNorm u₁ k) / (1 - γ₁ * γ₂) := by
  simpa using small_gain (hG₁.linear_zero_bias G₁) (hG₂.linear_zero_bias G₂) hγ₁ hγ₂ hγ h₁ h₂ k

end Linear

end ControlsLean.Controls
