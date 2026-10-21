/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Discrete-Time Control Barrier Functions (DTCBFs) & Willems Passivity Theory

This module formalizes two foundational pillars of modern nonlinear and safety-critical control:

1. **Discrete-Time Exponential Control Barrier Functions (DTCBFs)**:
   For a safety superlevel set $\mathcal{C} = \{x \in X \mid h(x) \ge 0\}$, the discrete-time
   barrier condition $\Delta h(x_k, u_k) = h(x_{k+1}) - h(x_k) \ge -\gamma h(x_k)$ with
   $0 \le \gamma \le 1$ guarantees:
   - `dtcbf_step_lower_bound`: $(1 - \gamma) h(x_k) \le h(x_{k+1})$.
   - `dtcbf_iterate_lower_bound`: Exponential lower envelope
     $(1 - \gamma)^k h(x_0) \le h(x_k)$ for all $k \in \mathbb{N}$.
   - `dtcbf_forward_invariant`: Forward invariance $h(x_0) \ge 0 \implies \forall k,\, h(x_k) \ge 0$.
   - `dtcbf_strict_forward_invariant`: Strict interior invariance
     $h(x_0) > 0 \wedge \gamma < 1 \implies \forall k,\, h(x_k) > 0$.

2. **Willems Dissipativity, Passivity & Negative Feedback Interconnections**:
   - `dissipative_telescoping_bound`: Stepwise supply inequality
     $V(k + 1) - V(k) \le s(k)$ implies $V(N) - V(0) \le \sum_{k=0}^{N-1} s(k)$.
   - `passive_extracted_energy_bound`: A passive system with nonnegative storage $V(N) \ge 0$ can
     never supply more energy to its environment than its initial stored energy $V(0)$:
     $\sum_{k=0}^{N-1} (-u_k \cdot y_k) \le V(0)$.
   - `passive_feedback_power_balance`: Negative feedback interconnection
     $u_1 = r_1 - y_2,\; u_2 = r_2 + y_1$ satisfies the Skew-Adjoint Power Identity
     $u_1 \cdot y_1 + u_2 \cdot y_2 = r_1 \cdot y_1 + r_2 \cdot y_2$.
   - `passive_feedback_dissipation`: Unforced ($r_1 = r_2 = 0$) negative feedback interconnection
     of two output-strictly passive systems decreases composite storage $V_1 + V_2$ at every step:
     $(V_1(k+1) + V_2(k+1)) - (V_1(k) + V_2(k)) \le -d_1(k) - d_2(k) \le 0$.
-/

namespace ControlsLean.Controls

open Finset Matrix

/-! ## 1. Discrete-Time Exponential Control Barrier Functions (DTCBFs) -/

/-- Stepwise equivalence between the DTCBF difference inequality
$h(x_{k+1}) - h(x_k) \ge -\gamma h(x_k)$ and the multiplicative lower bound
$(1 - \gamma) h(x_k) \le h(x_{k+1})$. -/
theorem dtcbf_step_lower_bound (h_curr h_next γ : ℝ) :
    -γ * h_curr ≤ h_next - h_curr ↔ (1 - γ) * h_curr ≤ h_next := by
  constructor <;> intro H <;> linarith

/-- **DTCBF Exponential Lower Envelope**:
Along any discrete-time trajectory $x : \mathbb{N} \to X$ satisfying
$h(x_{k+1}) - h(x_k) \ge -\gamma h(x_k)$ with $\gamma \le 1$, the barrier function satisfies
$(1 - \gamma)^k h(x_0) \le h(x_k)$ for all $k \in \mathbb{N}$. -/
theorem dtcbf_iterate_lower_bound {X : Type*} (h : X → ℝ) (x : ℕ → X) (γ : ℝ)
    (hγ : γ ≤ 1)
    (hcbf : ∀ k : ℕ, -γ * h (x k) ≤ h (x (k + 1)) - h (x k)) (k : ℕ) :
    (1 - γ) ^ k * h (x 0) ≤ h (x k) := by
  have h1γ : 0 ≤ 1 - γ := by linarith
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hstep : (1 - γ) * h (x k) ≤ h (x (k + 1)) :=
      (dtcbf_step_lower_bound (h (x k)) (h (x (k + 1))) γ).mp (hcbf k)
    calc (1 - γ) ^ (k + 1) * h (x 0)
        = (1 - γ) * ((1 - γ) ^ k * h (x 0)) := by rw [pow_succ']; ring
      _ ≤ (1 - γ) * h (x k) := mul_le_mul_of_nonneg_left ih h1γ
      _ ≤ h (x (k + 1)) := hstep

/-- **Forward Invariance of Safe Superlevel Sets under DTCBF**:
If $x_0$ starts in the safe set $\mathcal{C} = \{x \mid h(x) \ge 0\}$ ($0 \le h(x_0)$) and
$h(x_{k+1}) - h(x_k) \ge -\gamma h(x_k)$ holds with $\gamma \le 1$, then $x_k \in \mathcal{C}$
($0 \le h(x_k)$) for all $k \in \mathbb{N}$. -/
theorem dtcbf_forward_invariant {X : Type*} (h : X → ℝ) (x : ℕ → X) (γ : ℝ)
    (hγ : γ ≤ 1)
    (hcbf : ∀ k : ℕ, -γ * h (x k) ≤ h (x (k + 1)) - h (x k))
    (h0 : 0 ≤ h (x 0)) (k : ℕ) :
    0 ≤ h (x k) := by
  have h1γ : 0 ≤ 1 - γ := by linarith
  have hpow : 0 ≤ (1 - γ) ^ k * h (x 0) := mul_nonneg (pow_nonneg h1γ k) h0
  exact hpow.trans (dtcbf_iterate_lower_bound h x γ hγ hcbf k)

/-- **Strict Interior Forward Invariance under DTCBF**:
If $0 < h(x_0)$ and $\gamma < 1$, then $0 < h(x_k)$ for all $k \in \mathbb{N}$: the trajectory
never reaches the boundary $\{x \mid h(x) = 0\}$ in finite time. -/
theorem dtcbf_strict_forward_invariant {X : Type*} (h : X → ℝ) (x : ℕ → X) (γ : ℝ)
    (hγ : γ < 1)
    (hcbf : ∀ k : ℕ, -γ * h (x k) ≤ h (x (k + 1)) - h (x k))
    (h0 : 0 < h (x 0)) (k : ℕ) :
    0 < h (x k) := by
  have h1γ : 0 < 1 - γ := by linarith
  have hpow : 0 < (1 - γ) ^ k * h (x 0) := mul_pos (pow_pos h1γ k) h0
  exact lt_of_lt_of_le hpow (dtcbf_iterate_lower_bound h x γ hγ.le hcbf k)

/-! ## 2. Willems Dissipativity, Passivity & Negative Feedback Interconnections -/

/-- **Discrete-Time Dissipativity Telescoping Bound**:
If a storage sequence $V : \mathbb{N} \to \mathbb{R}$ and supply rate sequence
$s : \mathbb{N} \to \mathbb{R}$ satisfy the Willems dissipation inequality
$V(k + 1) - V(k) \le s(k)$ for all $k$, then over any finite horizon $N$:
$V(N) - V(0) \le \sum_{k=0}^{N-1} s(k)$. -/
theorem dissipative_telescoping_bound (V s : ℕ → ℝ)
    (hdiss : ∀ k : ℕ, V (k + 1) - V k ≤ s k) (N : ℕ) :
    V N - V 0 ≤ ∑ k ∈ range N, s k := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    rw [sum_range_succ]
    have hstep := hdiss N
    linarith

/-- **Passivity Extracted-Energy Bound**:
For a passive system with nonnegative storage ($0 \le V(N)$) and passivity inequality
$V(k + 1) - V(k) \le u_k \cdot y_k$, the total energy $\sum_{k=0}^{N-1} (-u_k \cdot y_k)$
extracted from the system over any horizon $N$ cannot exceed the initial stored energy $V(0)$. -/
theorem passive_extracted_energy_bound {m : Type*} [Fintype m]
    (V : ℕ → ℝ) (u y : ℕ → m → ℝ)
    (hpass : ∀ k : ℕ, V (k + 1) - V k ≤ u k ⬝ᵥ y k)
    (hV_nonneg : ∀ k : ℕ, 0 ≤ V k) (N : ℕ) :
    ∑ k ∈ range N, -(u k ⬝ᵥ y k) ≤ V 0 := by
  have ht := dissipative_telescoping_bound V (fun k => u k ⬝ᵥ y k) hpass N
  have hVN := hV_nonneg N
  rw [sum_neg_distrib]
  linarith

/-- **Negative Feedback Power Balance Identity**:
For two subsystems interconnected in standard negative feedback
$u_1 = r_1 - y_2$ and $u_2 = r_2 + y_1$, the internal interconnection is lossless:
$u_1 \cdot y_1 + u_2 \cdot y_2 = r_1 \cdot y_1 + r_2 \cdot y_2$. -/
theorem passive_feedback_power_balance {m : Type*} [Fintype m]
    (r₁ r₂ y₁ y₂ : m → ℝ) :
    (r₁ - y₂) ⬝ᵥ y₁ + (r₂ + y₁) ⬝ᵥ y₂ = r₁ ⬝ᵥ y₁ + r₂ ⬝ᵥ y₂ := by
  simp only [sub_dotProduct, add_dotProduct]
  have hcomm : y₂ ⬝ᵥ y₁ = y₁ ⬝ᵥ y₂ := dotProduct_comm y₂ y₁
  linarith

/-- **Unforced Negative Feedback Passivity Dissipation**:
When two output-strictly passive subsystems satisfying
$V_1(k+1) - V_1(k) \le u_1(k) \cdot y_1(k) - d_1(k)$ and
$V_2(k+1) - V_2(k) \le u_2(k) \cdot y_2(k) - d_2(k)$
are connected in unforced negative feedback ($u_1 = -y_2,\; u_2 = y_1$), the composite storage
$W(k) = V_1(k) + V_2(k)$ satisfies
$W(k+1) - W(k) \le -(d_1(k) + d_2(k))$ at every step $k$ and
$W(N) + \sum_{k=0}^{N-1} (d_1(k) + d_2(k)) \le W(0)$ over any horizon $N$. -/
theorem passive_feedback_dissipation {m : Type*} [Fintype m]
    (V₁ V₂ d₁ d₂ : ℕ → ℝ) (y₁ y₂ : ℕ → m → ℝ)
    (hpass₁ : ∀ k : ℕ, V₁ (k + 1) - V₁ k ≤ (-y₂ k) ⬝ᵥ y₁ k - d₁ k)
    (hpass₂ : ∀ k : ℕ, V₂ (k + 1) - V₂ k ≤ y₁ k ⬝ᵥ y₂ k - d₂ k)
    (N : ℕ) :
    (V₁ N + V₂ N) + ∑ k ∈ range N, (d₁ k + d₂ k) ≤ V₁ 0 + V₂ 0 := by
  have hstep : ∀ k : ℕ, (V₁ (k + 1) + V₂ (k + 1)) - (V₁ k + V₂ k) ≤ -(d₁ k + d₂ k) := by
    intro k
    have h1 := hpass₁ k
    have h2 := hpass₂ k
    have hcancel : (-y₂ k) ⬝ᵥ y₁ k + y₁ k ⬝ᵥ y₂ k = 0 := by
      rw [neg_dotProduct, dotProduct_comm (y₂ k) (y₁ k), neg_add_cancel]
    linarith
  have ht := dissipative_telescoping_bound (fun k => V₁ k + V₂ k) (fun k => -(d₁ k + d₂ k)) hstep N
  rw [sum_neg_distrib] at ht
  linarith

end ControlsLean.Controls
