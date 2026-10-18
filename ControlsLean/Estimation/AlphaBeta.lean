/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The steady-state α–β filter and the Kalata relation

Constant-velocity model with sample time `T`: state `(position, velocity)`,
`F = [[1, T], [0, 1]]`, position measurement `H = [1, 0]` with noise variance `r > 0`.
Process noise is the *discrete white-noise acceleration* (piecewise-constant acceleration)
model of Bar-Shalom: a constant acceleration of variance `q = σ_a²` acts over each sample, so
`Q = q g gᵀ` with `g = [T²/2, T]`, i.e. `Q = q [[T⁴/4, T³/2], [T³/2, T²]]`.

The steady-state (prior) covariance `P = [[p11, p12], [p12, p22]]` solves the discrete Riccati
equation `P = F (P - P Hᵀ (H P Hᵀ + r)⁻¹ H P) Fᵀ + Q`; `riccatiMap_eq_iff` writes it entrywise
as `IsSteadyState`. The steady-state gain is `K = [α, β/T]` with `α = p11 / (p11 + r)` and
`β = T p12 / (p11 + r)`.

* `gain_quadratic`: `α² = (2 - α) β - β² / 4`.
* `beta_sq_div`: `β² / (1 - α) = λ²` for the tracking index `λ = σ_a T² / σ_r`.
* `kalata`: for a positive semidefinite solution, `0 < α < 1`, `0 < β ≤ 2α`, and
  `β = 2 (2 - α) - 4 √(1 - α)`.
* `isSteadyState_of_gains`: conversely, gains satisfying these relations come from an explicit
  positive definite steady-state solution.
* `exists_gains`, `exists_steadyState`: for every `λ > 0` (resp. every `T, q, r > 0`) the
  relations have a solution, given in closed form via `u = √(1 - α)`, the root in `(0, 1)` of
  `u² - (2 + λ/2) u + 1 = 0`.

References: P. R. Kalata, "The tracking index: a generalized parameter for α-β and α-β-γ
target trackers", IEEE Trans. AES 20(2), 1984; Y. Bar-Shalom, X. R. Li, T. Kirubarajan,
*Estimation with Applications to Tracking and Navigation*, §6.3 and §6.5.
-/

namespace ControlsLean.Estimation.AlphaBeta

open Matrix

variable {T q r p11 p12 p22 α β lam : ℝ}

/-! ### The steady-state Riccati equation, entrywise -/

/-- Posterior covariance `P - P Hᵀ (H P Hᵀ + r)⁻¹ H P`, entry `(1,1)`; note `H P Hᵀ = p11`. -/
noncomputable def post11 (r p11 : ℝ) : ℝ := p11 - p11 ^ 2 / (p11 + r)

/-- Posterior covariance, entry `(1,2)`. -/
noncomputable def post12 (r p11 p12 : ℝ) : ℝ := p12 - p11 * p12 / (p11 + r)

/-- Posterior covariance, entry `(2,2)`. -/
noncomputable def post22 (r p11 p12 p22 : ℝ) : ℝ := p22 - p12 ^ 2 / (p11 + r)

/-- The steady-state Riccati equation `P = F M Fᵀ + Q` for the constant-velocity model,
with `M` the posterior covariance and `Q = q [[T⁴/4, T³/2], [T³/2, T²]]`. -/
structure IsSteadyState (T q r p11 p12 p22 : ℝ) : Prop where
  eq11 : p11 = post11 r p11 + 2 * T * post12 r p11 p12 + T ^ 2 * post22 r p11 p12 p22 +
    q * T ^ 4 / 4
  eq12 : p12 = post12 r p11 p12 + T * post22 r p11 p12 p22 + q * T ^ 3 / 2
  eq22 : p22 = post22 r p11 p12 p22 + q * T ^ 2

/-- Position gain `α = p11 / (p11 + r)`. -/
noncomputable def alpha (r p11 : ℝ) : ℝ := p11 / (p11 + r)

/-- Velocity gain times `T`: `β = T p12 / (p11 + r)`. -/
noncomputable def beta (T r p11 p12 : ℝ) : ℝ := T * p12 / (p11 + r)

/-- The tracking index `λ = σ_a T² / σ_r`, with `q = σ_a²` and `r = σ_r²`. -/
noncomputable def trackingIndex (T q r : ℝ) : ℝ := Real.sqrt q * T ^ 2 / Real.sqrt r

theorem trackingIndex_sq (hq : 0 ≤ q) (hr : 0 < r) :
    trackingIndex T q r ^ 2 = q * T ^ 4 / r := by
  unfold trackingIndex
  rw [div_pow, mul_pow, Real.sq_sqrt hq, Real.sq_sqrt hr.le]
  ring

theorem trackingIndex_pos (hT : 0 < T) (hq : 0 < q) (hr : 0 < r) : 0 < trackingIndex T q r := by
  unfold trackingIndex
  have := Real.sqrt_pos.2 hq
  have := Real.sqrt_pos.2 hr
  positivity

/-! ### Matrix form -/

/-- State transition of the constant-velocity model. -/
def F (T : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, T; 0, 1]

/-- Position measurement row. -/
def H : Fin 2 → ℝ := ![1, 0]

/-- Noise gain of a piecewise-constant acceleration over one sample. -/
noncomputable def g (T : ℝ) : Fin 2 → ℝ := ![T ^ 2 / 2, T]

/-- Discrete white-noise-acceleration covariance `q g gᵀ`. -/
noncomputable def Qmat (T q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := q • vecMulVec (g T) (g T)

/-- Symmetric covariance with entries `p11, p12, p22`. -/
def Pmat (p11 p12 p22 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![p11, p12; p12, p22]

/-- One predict+update step of the Riccati recursion (prior covariance to prior covariance). -/
noncomputable def riccatiMap (T q r : ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  F T * (P - (H ⬝ᵥ (P *ᵥ H) + r)⁻¹ • vecMulVec (P *ᵥ H) (H ᵥ* P)) * (F T)ᵀ + Qmat T q

/-- The Riccati map on a symmetric covariance, entrywise. -/
theorem riccatiMap_Pmat : riccatiMap T q r (Pmat p11 p12 p22) =
    !![post11 r p11 + 2 * T * post12 r p11 p12 + T ^ 2 * post22 r p11 p12 p22 + q * T ^ 4 / 4,
      post12 r p11 p12 + T * post22 r p11 p12 p22 + q * T ^ 3 / 2;
      post12 r p11 p12 + T * post22 r p11 p12 p22 + q * T ^ 3 / 2,
      post22 r p11 p12 p22 + q * T ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [riccatiMap, F, H, Qmat, g, Pmat, post11, post12, post22,
      Fin.sum_univ_two, dotProduct, mulVec, vecMul, Pi.smul_apply,
      vecHead, vecTail] <;> ring

/-- The matrix Riccati equation is exactly the entrywise system `IsSteadyState`. -/
theorem riccatiMap_eq_iff :
    riccatiMap T q r (Pmat p11 p12 p22) = Pmat p11 p12 p22 ↔ IsSteadyState T q r p11 p12 p22 := by
  rw [riccatiMap_Pmat, Pmat, ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one]
  constructor
  · rintro ⟨⟨h00, h01⟩, -, h11⟩
    exact ⟨h00.symm, h01.symm, h11.symm⟩
  · rintro ⟨h00, h01, h11⟩
    exact ⟨⟨h00.symm, h01.symm⟩, ⟨h01.symm, h11.symm⟩⟩

/-! ### Phase (a): from a steady-state solution to the Kalata relation -/

/-- The Riccati equation with denominators cleared (`s = p11 + r`). -/
theorem IsSteadyState.cleared (h : IsSteadyState T q r p11 p12 p22) (hs : p11 + r ≠ 0) :
    p12 ^ 2 = q * T ^ 2 * (p11 + r) ∧
    p11 * p12 = T * (p22 * (p11 + r) - p12 ^ 2) + q * T ^ 3 * (p11 + r) / 2 ∧
    p11 ^ 2 = 2 * T * p12 * r + T ^ 2 * (p22 * (p11 + r) - p12 ^ 2) +
      q * T ^ 4 * (p11 + r) / 4 := by
  obtain ⟨h11, h12, h22⟩ := h
  simp only [post11, post12, post22] at h11 h12 h22
  refine ⟨?_, ?_, ?_⟩
  · field_simp at h22; linear_combination h22
  · field_simp at h12; linear_combination h12 / 2
  · field_simp at h11; linear_combination h11 / 4

/-- **Gain quadratic**: `α² = (2 - α) β - β² / 4`. -/
theorem gain_quadratic (h : IsSteadyState T q r p11 p12 p22) (hs : p11 + r ≠ 0) :
    alpha r p11 ^ 2 = (2 - alpha r p11) * beta T r p11 p12 - beta T r p11 p12 ^ 2 / 4 := by
  obtain ⟨e22, e12, e11⟩ := h.cleared hs
  unfold alpha beta
  field_simp
  linear_combination 4 * e11 - 4 * T * e12 + T ^ 2 * e22

/-- **Tracking index**: `β² / (1 - α) = λ² = q T⁴ / r`. -/
theorem beta_sq_div (h : IsSteadyState T q r p11 p12 p22) (hp : 0 ≤ p11) (hq : 0 ≤ q)
    (hr : 0 < r) : beta T r p11 p12 ^ 2 / (1 - alpha r p11) = trackingIndex T q r ^ 2 := by
  have hs : p11 + r ≠ 0 := by positivity
  obtain ⟨e22, -, -⟩ := h.cleared hs
  rw [trackingIndex_sq hq hr]
  unfold alpha beta
  have h1 : 1 - p11 / (p11 + r) = r / (p11 + r) := by field_simp; ring
  rw [h1]
  field_simp
  linear_combination T ^ 2 * e22

/-- The Kalata relation picks the smaller root of the gain quadratic once `β ≤ 2α`. -/
theorem kalata_of_quadratic (hα : α ≤ 1) (hβ : β ≤ 2 * α)
    (hq : α ^ 2 = (2 - α) * β - β ^ 2 / 4) : β = 2 * (2 - α) - 4 * Real.sqrt (1 - α) := by
  have hnn : 0 ≤ (2 * (2 - α) - β) / 4 := by linarith
  have : 1 - α = ((2 * (2 - α) - β) / 4) ^ 2 := by linear_combination -hq / 4
  rw [this, Real.sqrt_sq hnn]
  ring

/-- **Kalata relation.** For a positive semidefinite steady-state solution with `p11 > 0`,
the gains satisfy `0 < α < 1`, `0 < β ≤ 2α` and `β = 2 (2 - α) - 4 √(1 - α)`. -/
theorem kalata (h : IsSteadyState T q r p11 p12 p22) (hT : 0 < T) (hq : 0 < q) (hr : 0 < r)
    (hp : 0 < p11) (hpsd : p12 ^ 2 ≤ p11 * p22) :
    (0 < alpha r p11 ∧ alpha r p11 < 1) ∧ (0 < beta T r p11 p12 ∧
      beta T r p11 p12 ≤ 2 * alpha r p11) ∧
    beta T r p11 p12 = 2 * (2 - alpha r p11) - 4 * Real.sqrt (1 - alpha r p11) := by
  have hs : 0 < p11 + r := by positivity
  obtain ⟨e22, e12, -⟩ := h.cleared hs.ne'
  have hp22 : 0 ≤ p22 := by
    by_contra h'; nlinarith [sq_nonneg p12]
  have hm : 0 ≤ p22 * (p11 + r) - p12 ^ 2 := by nlinarith
  -- `T · (p22 s - p12²) = p12 (p11 - T p12 / 2)`
  have key : T * (p22 * (p11 + r) - p12 ^ 2) = p12 * (p11 - T * p12 / 2) := by
    linear_combination -e12 + T / 2 * e22
  have hprod : 0 ≤ p12 * (2 * p11 - T * p12) := by nlinarith
  have hp12 : 0 < p12 := by
    rcases lt_trichotomy p12 0 with h' | h' | h'
    · nlinarith
    · subst h'; nlinarith [mul_pos (mul_pos hq (pow_pos hT 2)) hs]
    · exact h'
  have hTp : T * p12 ≤ 2 * p11 := by nlinarith
  have hα : 0 < alpha r p11 ∧ alpha r p11 < 1 := by
    unfold alpha
    exact ⟨by positivity, by rw [div_lt_one hs]; linarith⟩
  have hβ : 0 < beta T r p11 p12 ∧ beta T r p11 p12 ≤ 2 * alpha r p11 := by
    unfold alpha beta
    refine ⟨by positivity, ?_⟩
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hs]
    exact hTp
  exact ⟨hα, hβ, kalata_of_quadratic hα.2.le hβ.2 (gain_quadratic h hs.ne')⟩

/-! ### Phase (b): existence -/

/-- Conversely, gains `0 < α < 1`, `0 < β ≤ 2α` satisfying the gain quadratic and
`β² r = q T⁴ (1 - α)` come from an explicit positive definite steady-state solution. -/
theorem isSteadyState_of_gains (hT : 0 < T) (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ : β ≤ 2 * α) (hquad : α ^ 2 = (2 - α) * β - β ^ 2 / 4)
    (hlam : β ^ 2 * r = q * T ^ 4 * (1 - α)) :
    ∃ p11 p12 p22 : ℝ, IsSteadyState T q r p11 p12 p22 ∧ 0 < p11 ∧ p12 ^ 2 < p11 * p22 ∧
      alpha r p11 = α ∧ beta T r p11 p12 = β := by
  set s := r / (1 - α) with hs_def
  have h1α : 0 < 1 - α := by linarith
  have hs : 0 < s := by positivity
  have hsr : r = s * (1 - α) := by rw [hs_def]; field_simp
  have hden : α * s + r = s := by rw [hsr]; ring
  have hqs : q * T ^ 4 = β ^ 2 * s := mul_right_cancel₀ h1α.ne' (by
    linear_combination -hlam + β ^ 2 * hsr)
  refine ⟨α * s, β * s / T, s * β * (α + β / 2) / T ^ 2, ⟨?_, ?_, ?_⟩, by positivity, ?_, ?_, ?_⟩
  · unfold post11 post12 post22
    rw [hden]
    field_simp
    linear_combination 8 * s * hquad - 2 * hqs
  · unfold post12 post22
    rw [hden]
    field_simp
    linear_combination -hqs
  · unfold post22
    rw [hden]
    field_simp
    linear_combination -2 * hqs
  · have hk : α * β * (α + β / 2) - β ^ 2 = β ^ 2 * (4 - 2 * α - β) / 4 := by
      linear_combination β * hquad
    have hk0 : 0 < β ^ 2 * (4 - 2 * α - β) / 4 := by
      have : 0 < 4 - 2 * α - β := by linarith
      positivity
    have e : α * s * (s * β * (α + β / 2) / T ^ 2) = α * β * (α + β / 2) * s ^ 2 / T ^ 2 := by
      ring
    rw [e, div_pow, mul_pow]
    gcongr
    nlinarith [mul_pos hk0 (pow_pos hs 2)]
  · unfold alpha; rw [hden]; field_simp
  · unfold beta; rw [hden]; field_simp

/-- `u = √(1 - α)` as a function of the tracking index: the root in `(0, 1)` of
`u² - (2 + λ/2) u + 1 = 0`. -/
noncomputable def kalataU (lam : ℝ) : ℝ :=
  ((2 + lam / 2) - Real.sqrt ((2 + lam / 2) ^ 2 - 4)) / 2

theorem kalataU_spec (hlam : 0 < lam) :
    0 < kalataU lam ∧ kalataU lam < 1 ∧ 2 * (1 - kalataU lam) ^ 2 = lam * kalataU lam := by
  unfold kalataU
  set c := 2 + lam / 2 with hc_def
  have hc : 2 < c := by linarith
  have hd := Real.sq_sqrt (show 0 ≤ c ^ 2 - 4 by nlinarith)
  have hd0 := Real.sqrt_nonneg (c ^ 2 - 4)
  set d := Real.sqrt (c ^ 2 - 4)
  have hdc : d < c := by nlinarith
  have hcd : c - 2 < d := by nlinarith
  refine ⟨by linarith, by linarith, ?_⟩
  linear_combination hd / 2 + (c - d) * hc_def

/-- **Existence of α–β gains** for every tracking index `λ > 0`, in closed form
`α = 1 - u²`, `β = 2 (1 - u)²` with `u = kalataU λ`. -/
theorem exists_gains (hlam : 0 < lam) :
    ∃ α β : ℝ, (0 < α ∧ α < 1) ∧ (0 < β ∧ β ≤ 2 * α) ∧
      α ^ 2 = (2 - α) * β - β ^ 2 / 4 ∧ β = 2 * (2 - α) - 4 * Real.sqrt (1 - α) ∧
      β ^ 2 / (1 - α) = lam ^ 2 := by
  obtain ⟨hu0, hu1, hu⟩ := kalataU_spec hlam
  set u := kalataU lam
  have hsq : Real.sqrt (1 - (1 - u ^ 2)) = u := by
    rw [show 1 - (1 - u ^ 2) = u ^ 2 by ring, Real.sqrt_sq hu0.le]
  refine ⟨1 - u ^ 2, 2 * (1 - u) ^ 2, ⟨by nlinarith, by nlinarith⟩,
    ⟨by have : 0 < 1 - u := by linarith
        positivity, by nlinarith⟩, by ring, by rw [hsq]; ring, ?_⟩
  rw [div_eq_iff (by nlinarith)]
  linear_combination (2 * (1 - u) ^ 2 + lam * u) * hu

/-- **Existence of the steady state**: for all `T, q, r > 0` the Riccati equation has a
positive definite solution (whose gains then satisfy `kalata`). -/
theorem exists_steadyState (hT : 0 < T) (hq : 0 < q) (hr : 0 < r) :
    ∃ p11 p12 p22 : ℝ, IsSteadyState T q r p11 p12 p22 ∧ 0 < p11 ∧ p12 ^ 2 < p11 * p22 := by
  obtain ⟨α, β, hα, hβ, hquad, -, hlam⟩ := exists_gains (trackingIndex_pos hT hq hr)
  rw [trackingIndex_sq hq.le hr, div_eq_iff (by linarith)] at hlam
  obtain ⟨p11, p12, p22, h, hp, hpsd, -⟩ := isSteadyState_of_gains hT hr hα.1 hα.2 hβ.1 hβ.2
    hquad (by rw [hlam]; field_simp)
  exact ⟨p11, p12, p22, h, hp, hpsd⟩

end ControlsLean.Estimation.AlphaBeta
