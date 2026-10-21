/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Estimation.ScalarKalman
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence of the scalar Riccati iteration

For the random walk `x_{k+1} = x_k + w` (`Var w = Q > 0`) observed through `z = x + v`
(`Var v = R > 0`), the prior error variance of the Kalman filter evolves by
`P_{k+1} = riccati R Q P_k = P_k R / (P_k + R) + Q`.

* From any initial variance `P₀ ≥ 0`, every iterate after the first is `≥ Q`
  (`le_riccati_iterate`).
* On `[Q, ∞)` the Riccati map contracts towards the steady state `S = steadyState R Q` with
  factor `c = (R / (Q + R))² < 1` (`abs_riccati_sub_steadyState_le`).
* Hence `|P_{k+1} - S| ≤ cᵏ |P₁ - S|` (`abs_riccati_iterate_sub_le`) and
  `P_k → S` (`tendsto_riccati_iterate`).
* Consequently the Kalman gain `P_k / (P_k + R)` converges to the steady-state gain
  `S / (S + R)` (`tendsto_gain_riccati_iterate`).

The contraction factor of `riccati_lipschitz` depends on `min P₁ P₂`, so it is only uniform
once the iterates are bounded below; the bound `P_k ≥ Q` for `k ≥ 1` supplies this.
-/

namespace ControlsLean.Estimation

open Filter Topology

variable {R Q P P₀ : ℝ}

theorem postVarOpt_nonneg (hP : 0 ≤ P) (hR : 0 < R) : 0 ≤ postVarOpt P R := by
  unfold postVarOpt; positivity

/-- The Riccati map never goes below the process noise `Q`. -/
theorem le_riccati (hR : 0 < R) (hP : 0 ≤ P) : Q ≤ riccati R Q P := by
  unfold riccati; linarith [postVarOpt_nonneg hP hR]

theorem lt_steadyState (hR : 0 < R) (hQ : 0 < Q) : Q < steadyState R Q := by
  unfold steadyState
  have : Q < Real.sqrt (Q ^ 2 + 4 * Q * R) := by
    rw [Real.lt_sqrt hQ.le]; nlinarith
  linarith

theorem riccati_iterate_nonneg (hR : 0 < R) (hQ : 0 < Q) (hP₀ : 0 ≤ P₀) (k : ℕ) :
    0 ≤ (riccati R Q)^[k] P₀ := by
  induction k with
  | zero => exact hP₀
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hQ.le.trans (le_riccati hR ih)

/-- After one step, every iterate is at least `Q`. -/
theorem le_riccati_iterate (hR : 0 < R) (hQ : 0 < Q) (hP₀ : 0 ≤ P₀) (k : ℕ) :
    Q ≤ (riccati R Q)^[k + 1] P₀ := by
  rw [Function.iterate_succ_apply']
  exact le_riccati hR (riccati_iterate_nonneg hR hQ hP₀ k)

/-- **Uniform contraction towards the steady state** on `[Q, ∞)`. -/
theorem abs_riccati_sub_steadyState_le (hR : 0 < R) (hQ : 0 < Q) (hP : Q ≤ P) :
    |riccati R Q P - steadyState R Q| ≤ (R / (Q + R)) ^ 2 * |P - steadyState R Q| := by
  have hS := lt_steadyState hR hQ
  conv_lhs => rw [← riccati_steadyState hR hQ]
  refine (riccati_lipschitz hR (by linarith) (by linarith)).trans ?_
  have hmin : Q ≤ min P (steadyState R Q) := le_min hP hS.le
  have : R / (min P (steadyState R Q) + R) ≤ R / (Q + R) :=
    div_le_div_of_nonneg_left hR.le (by positivity) (by linarith)
  gcongr
  exact div_nonneg hR.le (by linarith)

theorem riccati_rate_lt_one (hR : 0 < R) (hQ : 0 < Q) : (R / (Q + R)) ^ 2 < 1 := by
  have h0 : 0 ≤ R / (Q + R) := by positivity
  have h1 : R / (Q + R) < 1 := by rw [div_lt_one (by positivity)]; linarith
  nlinarith

/-- **Geometric convergence rate**: `|P_{k+1} - S| ≤ ((R / (Q + R))²)ᵏ |P₁ - S|`. -/
theorem abs_riccati_iterate_sub_le (hR : 0 < R) (hQ : 0 < Q) (hP₀ : 0 ≤ P₀) (k : ℕ) :
    |(riccati R Q)^[k + 1] P₀ - steadyState R Q| ≤
      ((R / (Q + R)) ^ 2) ^ k * |riccati R Q P₀ - steadyState R Q| := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc _ ≤ (R / (Q + R)) ^ 2 * |(riccati R Q)^[k + 1] P₀ - steadyState R Q| :=
          abs_riccati_sub_steadyState_le hR hQ (le_riccati_iterate hR hQ hP₀ k)
      _ ≤ (R / (Q + R)) ^ 2 * (((R / (Q + R)) ^ 2) ^ k *
            |riccati R Q P₀ - steadyState R Q|) := by gcongr
      _ = _ := by ring

/-- **Riccati convergence**: from any `P₀ ≥ 0`, the iterates converge to the steady state. -/
theorem tendsto_riccati_iterate (hR : 0 < R) (hQ : 0 < Q) (hP₀ : 0 ≤ P₀) :
    Tendsto (fun k => (riccati R Q)^[k] P₀) atTop (𝓝 (steadyState R Q)) := by
  rw [← tendsto_add_atTop_iff_nat 1, tendsto_iff_norm_sub_tendsto_zero]
  have hc := riccati_rate_lt_one hR hQ
  have hlim : Tendsto (fun k : ℕ => ((R / (Q + R)) ^ 2) ^ k *
      |riccati R Q P₀ - steadyState R Q|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hc).mul_const
      |riccati R Q P₀ - steadyState R Q|
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hlim
  rw [Real.norm_eq_abs]
  exact abs_riccati_iterate_sub_le hR hQ hP₀ k

/-- The Kalman gain converges to the steady-state gain `S / (S + R)`. -/
theorem tendsto_gain_riccati_iterate (hR : 0 < R) (hQ : 0 < Q) (hP₀ : 0 ≤ P₀) :
    Tendsto (fun k => gain ((riccati R Q)^[k] P₀) R) atTop
      (𝓝 (gain (steadyState R Q) R)) := by
  have h := tendsto_riccati_iterate hR hQ hP₀
  exact h.div (h.add_const R) (by linarith [steadyState_pos R hQ])

end ControlsLean.Estimation
