/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Nonlinear Integrator Backstepping & Control Lyapunov Functions (CLFs)

This module formalizes **Nonlinear Integrator Backstepping** and **Control Lyapunov Functions**
(closing Roadmap §4.2), following Krstić, Kanellakopoulos, & Kokotović (1995) and Sontag (1989).

## Main Results

1. **Continuous-Time Strict-Feedback Integrator Backstepping (`HasDerivAt`)**:
   - Consider the cascade / strict-feedback nonlinear plant
     $$\dot{x}_1 = f_1(x_1) + g_1(x_1) x_2, \qquad \dot{x}_2 = f_2(x_1, x_2) + g_2(x_1, x_2) u$$
     equipped with a virtual control $\alpha_1(x_1)$ and storage function $V_1(x_1)$.
   - `backsteppingError`: The backstepping error coordinate $z_2 = x_2 - \alpha_1(x_1)$.
   - `backsteppingLyapunov`: The augmented Lyapunov function
     $$V_2(x_1, x_2) = V_1(x_1) + \frac{1}{2} (x_2 - \alpha_1(x_1))^2.$$
   - `backstepping_lie_deriv_eq`: Exact Lie-derivative decomposition splitting the virtual-control
     dissipation $dV_1(x_1)(f_1(x_1) + g_1(x_1)\alpha_1(x_1))$ from the cross-coupling term
     $z_2 g_1(x_1) dV_1(x_1)$.
   - `hasDerivAt_backstepping_lyapunov`: Genuine `HasDerivAt` chain-rule derivation along any
     differentiable trajectory $(x_1(t), x_2(t))$.
   - `backsteppingControl`: Explicit recursive backstepping control law $u^*(x_1, x_2)$.
   - `backstepping_closedLoop_lie_deriv` & `hasDerivAt_backstepping_closedLoop`: Under
     $u = u^*(x_1, x_2)$, the interconnection cross-term $z_2 g_1(x_1) dV_1(x_1)$ cancels
     identically, yielding
     $$\dot{V}_2(x_1, x_2) = dV_1(x_1)\bigl(f_1(x_1) + g_1(x_1)\alpha_1(x_1)\bigr)
       - c_2 (x_2 - \alpha_1(x_1))^2.$$
   - `backstepping_dissipation_bound` & `backstepping_strict_negDef`: Strict negative definiteness
     of $\dot{V}_2$ for all $(x_1, x_2) \ne (0, 0)$ whenever $\alpha_1(0) = 0$ and $c_2 > 0$.

2. **Recursive $n$-Step Tridiagonal Skew-Symmetric Backstepping Cascade**:
   - `backstepping_step_dissipation`: Single-step inductive cancellation of the skew-symmetric
     coupling $z_{k-1} g_{k-1} z_k$.
   - `backstepping_chain_dissipation` & `hasDerivAt_backstepping_chain`: Telescoping cancellation
     across an $n$-integrator strict-feedback chain in error coordinates $z_0, \dots, z_{n-1}$,
     yielding $\frac{d}{dt} \left(\frac{1}{2} \sum_{i=0}^{n-1} z_i(t)^2\right) =
     -\sum_{i=0}^{n-1} c_i z_i(t)^2$.

3. **Sontag's Universal Control Lyapunov Function (CLF) Formula**:
   - `sontagControl`: Sontag's universal feedback law
     $$u_{\text{Sontag}}(a, b) = \begin{cases} 0 & \text{if } b = 0, \\
       -\dfrac{a + \sqrt{a^2 + b^4}}{b} & \text{if } b \ne 0. \end{cases}$$
   - `sontag_universal_stabilizer`: For $b \ne 0$,
     $a + b \cdot u_{\text{Sontag}}(a, b) = -\sqrt{a^2 + b^4} < 0$.
   - `sontag_clf_strict_decrease`: Under Artstein's CLF condition ($b = 0 \implies a < 0$),
     $a + b \cdot u_{\text{Sontag}}(a, b) < 0$ unconditionally across both $b = 0$ and $b \ne 0$.

## References

- M. Krstić, I. Kanellakopoulos, P. Kokotović, *Nonlinear and Adaptive Control Design*, Wiley (1995).
- E. D. Sontag, *A 'universal' construction of Artstein's theorem on nonlinear stabilization*,
  Systems & Control Letters 13 (1989), 117–123.
-/

namespace ControlsLean.Controls

open Finset BigOperators

/-! ### 1. Strict-Feedback Integrator Backstepping & `HasDerivAt` Calculus -/

/-- The backstepping error coordinate $z_2 = x_2 - \alpha_1(x_1)$, measuring deviation of $x_2$
from the virtual stabilizing control $\alpha_1(x_1)$. -/
def backsteppingError (α₁ : ℝ → ℝ) (x₁ x₂ : ℝ) : ℝ :=
  x₂ - α₁ x₁

/-- The augmented backstepping Control Lyapunov Function:
$$V_2(x_1, x_2) = V_1(x_1) + \frac{1}{2} (x_2 - \alpha_1(x_1))^2.$$ -/
noncomputable def backsteppingLyapunov (V₁ α₁ : ℝ → ℝ) (x₁ x₂ : ℝ) : ℝ :=
  V₁ x₁ + (1 / 2 : ℝ) * (x₂ - α₁ x₁) ^ 2

/-- Positive definiteness of `backsteppingLyapunov`: if $V_1(0) = 0$, $\alpha_1(0) = 0$, and
$V_1(x_1) > 0$ for $x_1 \ne 0$, then $V_2(0, 0) = 0$, $V_2(x_1, x_2) \ge 0$ everywhere, and
$V_2(x_1, x_2) > 0$ whenever $(x_1, x_2) \ne (0, 0)$. -/
theorem backsteppingLyapunov_posDef {V₁ α₁ : ℝ → ℝ}
    (hV₁0 : V₁ 0 = 0) (hα₁0 : α₁ 0 = 0)
    (hV₁_pos : ∀ x₁ ≠ 0, 0 < V₁ x₁) :
    backsteppingLyapunov V₁ α₁ 0 0 = 0 ∧
      (∀ x₁ x₂, 0 ≤ backsteppingLyapunov V₁ α₁ x₁ x₂) ∧
      (∀ x₁ x₂, (x₁ ≠ 0 ∨ x₂ ≠ 0) → 0 < backsteppingLyapunov V₁ α₁ x₁ x₂) := by
  have hV₁_nonneg : ∀ x₁, 0 ≤ V₁ x₁ := fun x₁ => by
    rcases eq_or_ne x₁ 0 with rfl | hx₁
    · exact hV₁0.ge
    · exact (hV₁_pos x₁ hx₁).le
  refine ⟨by simp [backsteppingLyapunov, hV₁0, hα₁0], fun x₁ x₂ => ?_, fun x₁ x₂ hne => ?_⟩
  · unfold backsteppingLyapunov
    exact add_nonneg (hV₁_nonneg x₁) (by positivity)
  · unfold backsteppingLyapunov
    rcases eq_or_ne x₁ 0 with rfl | hx₁
    · rcases hne with h1 | hx₂
      · exact (h1 rfl).elim
      · rw [hV₁0, hα₁0, zero_add, sub_zero]
        exact mul_pos (by norm_num) (sq_pos_of_ne_zero hx₂)
    · have h1 : 0 < V₁ x₁ := hV₁_pos x₁ hx₁
      have h2 : 0 ≤ (1 / 2 : ℝ) * (x₂ - α₁ x₁) ^ 2 := by positivity
      linarith

/-- **Exact Backstepping Lie-Derivative Decomposition (`backstepping_lie_deriv_eq`)**:
Writing $x_2 = \alpha_1(x_1) + (x_2 - \alpha_1(x_1))$ splits the Lie derivative of $V_2$ along
$\dot{x}_1 = f_1(x_1) + g_1(x_1) x_2$, $\dot{x}_2 = f_2(x_1, x_2) + g_2(x_1, x_2) u$ into the
virtual-control Lie derivative plus a single factorized error term:
$$\nabla V_1(x_1)(f_1(x_1) + g_1(x_1) x_2) +
  (x_2 - \alpha_1(x_1))\bigl(f_2(x_1, x_2) + g_2(x_1, x_2) u - \alpha_1'(x_1)(f_1(x_1) + g_1(x_1) x_2)\bigr)$$
$$= \nabla V_1(x_1)(f_1(x_1) + g_1(x_1)\alpha_1(x_1)) +
  (x_2 - \alpha_1(x_1))\bigl(g_1(x_1)\nabla V_1(x_1) + f_2(x_1, x_2) + g_2(x_1, x_2) u
    - \alpha_1'(x_1)(f_1(x_1) + g_1(x_1) x_2)\bigr).$$ -/
theorem backstepping_lie_deriv_eq (dV₁ f₁ g₁ α₁ dα₁ : ℝ → ℝ) (f₂ g₂ : ℝ → ℝ → ℝ)
    (x₁ x₂ u : ℝ) :
    dV₁ x₁ * (f₁ x₁ + g₁ x₁ * x₂) +
      (x₂ - α₁ x₁) * (f₂ x₁ x₂ + g₂ x₁ x₂ * u - dα₁ x₁ * (f₁ x₁ + g₁ x₁ * x₂)) =
    dV₁ x₁ * (f₁ x₁ + g₁ x₁ * α₁ x₁) +
      (x₂ - α₁ x₁) * (g₁ x₁ * dV₁ x₁ + f₂ x₁ x₂ + g₂ x₁ x₂ * u -
        dα₁ x₁ * (f₁ x₁ + g₁ x₁ * x₂)) := by
  ring

/-- **Genuine `HasDerivAt` Chain Rule for the Backstepping Lyapunov Function**:
Along any differentiable state trajectory $(x_1(t), x_2(t))$ satisfying
$\dot{x}_1(t) = f_1(x_1(t)) + g_1(x_1(t)) x_2(t)$ and
$\dot{x}_2(t) = f_2(x_1(t), x_2(t)) + g_2(x_1(t), x_2(t)) u$,
the composite function $s \mapsto V_2(x_1(s), x_2(s))$ has time derivative equal to the
decomposed backstepping Lie derivative. -/
theorem hasDerivAt_backstepping_lyapunov {V₁ dV₁ f₁ g₁ α₁ dα₁ : ℝ → ℝ}
    {f₂ g₂ : ℝ → ℝ → ℝ} {x₁ x₂ : ℝ → ℝ} {u t : ℝ}
    (hV₁ : HasDerivAt V₁ (dV₁ (x₁ t)) (x₁ t))
    (hα₁ : HasDerivAt α₁ (dα₁ (x₁ t)) (x₁ t))
    (hx₁ : HasDerivAt x₁ (f₁ (x₁ t) + g₁ (x₁ t) * x₂ t) t)
    (hx₂ : HasDerivAt x₂ (f₂ (x₁ t) (x₂ t) + g₂ (x₁ t) (x₂ t) * u) t) :
    HasDerivAt (fun s => backsteppingLyapunov V₁ α₁ (x₁ s) (x₂ s))
      (dV₁ (x₁ t) * (f₁ (x₁ t) + g₁ (x₁ t) * α₁ (x₁ t)) +
        (x₂ t - α₁ (x₁ t)) * (g₁ (x₁ t) * dV₁ (x₁ t) + f₂ (x₁ t) (x₂ t) +
          g₂ (x₁ t) (x₂ t) * u - dα₁ (x₁ t) * (f₁ (x₁ t) + g₁ (x₁ t) * x₂ t))) t := by
  have hV₁_comp : HasDerivAt (fun s => V₁ (x₁ s))
      (dV₁ (x₁ t) * (f₁ (x₁ t) + g₁ (x₁ t) * x₂ t)) t :=
    hV₁.comp t hx₁
  have hα₁_comp : HasDerivAt (fun s => α₁ (x₁ s))
      (dα₁ (x₁ t) * (f₁ (x₁ t) + g₁ (x₁ t) * x₂ t)) t :=
    hα₁.comp t hx₁
  have hz : HasDerivAt (fun s => x₂ s - α₁ (x₁ s))
      (f₂ (x₁ t) (x₂ t) + g₂ (x₁ t) (x₂ t) * u -
        dα₁ (x₁ t) * (f₁ (x₁ t) + g₁ (x₁ t) * x₂ t)) t :=
    hx₂.sub hα₁_comp
  have hz_sq : HasDerivAt (fun s => (x₂ s - α₁ (x₁ s)) ^ 2)
      (((2 : ℕ) : ℝ) * (x₂ t - α₁ (x₁ t)) ^ (2 - 1) *
        (f₂ (x₁ t) (x₂ t) + g₂ (x₁ t) (x₂ t) * u -
          dα₁ (x₁ t) * (f₁ (x₁ t) + g₁ (x₁ t) * x₂ t))) t :=
    hz.pow 2
  have h_sum := hV₁_comp.add (hz_sq.const_mul (1 / 2 : ℝ))
  refine h_sum.congr_deriv ?_
  push_cast
  rw [← backstepping_lie_deriv_eq]
  ring

/-- **The Recursive Backstepping Feedback Control Law**:
$$u^*(x_1, x_2) = g_2(x_1, x_2)^{-1}\bigl(-g_1(x_1)\nabla V_1(x_1) - f_2(x_1, x_2)
  + \alpha_1'(x_1)(f_1(x_1) + g_1(x_1) x_2) - c_2 (x_2 - \alpha_1(x_1))\bigr).$$ -/
noncomputable def backsteppingControl (dV₁ f₁ g₁ α₁ dα₁ : ℝ → ℝ) (f₂ g₂ : ℝ → ℝ → ℝ)
    (c₂ x₁ x₂ : ℝ) : ℝ :=
  (g₂ x₁ x₂)⁻¹ * (-g₁ x₁ * dV₁ x₁ - f₂ x₁ x₂ +
    dα₁ x₁ * (f₁ x₁ + g₁ x₁ * x₂) - c₂ * (x₂ - α₁ x₁))

/-- **Exact Cross-Term Cancellation under Backstepping Feedback**:
When $g_2(x_1, x_2) \ne 0$ and $u = \operatorname{backsteppingControl}$, the Lie derivative of
$V_2$ reduces identically to
$$\nabla V_1(x_1)\bigl(f_1(x_1) + g_1(x_1)\alpha_1(x_1)\bigr) - c_2 (x_2 - \alpha_1(x_1))^2.$$ -/
theorem backstepping_closedLoop_lie_deriv (dV₁ f₁ g₁ α₁ dα₁ : ℝ → ℝ) (f₂ g₂ : ℝ → ℝ → ℝ)
    (c₂ x₁ x₂ : ℝ) (hg₂ : g₂ x₁ x₂ ≠ 0) :
    let u := backsteppingControl dV₁ f₁ g₁ α₁ dα₁ f₂ g₂ c₂ x₁ x₂
    dV₁ x₁ * (f₁ x₁ + g₁ x₁ * x₂) +
      (x₂ - α₁ x₁) * (f₂ x₁ x₂ + g₂ x₁ x₂ * u - dα₁ x₁ * (f₁ x₁ + g₁ x₁ * x₂)) =
    dV₁ x₁ * (f₁ x₁ + g₁ x₁ * α₁ x₁) - c₂ * (x₂ - α₁ x₁) ^ 2 := by
  intro u
  rw [backstepping_lie_deriv_eq]
  dsimp [u, backsteppingControl]
  rw [mul_inv_cancel_left₀ hg₂]
  ring

/-- **Genuine `HasDerivAt` Closed-Loop Backstepping Theorem**:
Along any trajectory $(x_1(t), x_2(t))$ driven by `backsteppingControl` with
$g_2(x_1(t), x_2(t)) \ne 0$, the augmented Lyapunov function $V_2(x_1(t), x_2(t))$ has time
derivative
$$\dot{V}_2(t) = \nabla V_1(x_1(t))\bigl(f_1(x_1(t)) + g_1(x_1(t))\alpha_1(x_1(t))\bigr)
  - c_2 (x_2(t) - \alpha_1(x_1(t)))^2.$$ -/
theorem hasDerivAt_backstepping_closedLoop {V₁ dV₁ f₁ g₁ α₁ dα₁ : ℝ → ℝ}
    {f₂ g₂ : ℝ → ℝ → ℝ} {x₁ x₂ : ℝ → ℝ} {c₂ t : ℝ}
    (hg₂ : g₂ (x₁ t) (x₂ t) ≠ 0)
    (hV₁ : HasDerivAt V₁ (dV₁ (x₁ t)) (x₁ t))
    (hα₁ : HasDerivAt α₁ (dα₁ (x₁ t)) (x₁ t))
    (hx₁ : HasDerivAt x₁ (f₁ (x₁ t) + g₁ (x₁ t) * x₂ t) t)
    (hx₂ : HasDerivAt x₂ (f₂ (x₁ t) (x₂ t) + g₂ (x₁ t) (x₂ t) *
      backsteppingControl dV₁ f₁ g₁ α₁ dα₁ f₂ g₂ c₂ (x₁ t) (x₂ t)) t) :
    HasDerivAt (fun s => backsteppingLyapunov V₁ α₁ (x₁ s) (x₂ s))
      (dV₁ (x₁ t) * (f₁ (x₁ t) + g₁ (x₁ t) * α₁ (x₁ t)) -
        c₂ * (x₂ t - α₁ (x₁ t)) ^ 2) t := by
  have h := hasDerivAt_backstepping_lyapunov hV₁ hα₁ hx₁ hx₂
  refine h.congr_deriv ?_
  rw [← backstepping_lie_deriv_eq]
  exact backstepping_closedLoop_lie_deriv dV₁ f₁ g₁ α₁ dα₁ f₂ g₂ c₂ (x₁ t) (x₂ t) hg₂

/-- **Backstepping Dissipation Inequality**:
If the virtual control $\alpha_1(x_1)$ satisfies the subsystem dissipation bound
$\nabla V_1(x_1)(f_1(x_1) + g_1(x_1)\alpha_1(x_1)) \le -W_1(x_1)$, then the closed-loop
backstepping Lie derivative satisfies
$$\dot{V}_2(x_1, x_2) \le -W_1(x_1) - c_2 (x_2 - \alpha_1(x_1))^2.$$ -/
theorem backstepping_dissipation_bound {dV₁ f₁ g₁ α₁ dα₁ W₁ : ℝ → ℝ}
    {f₂ g₂ : ℝ → ℝ → ℝ} {c₂ x₁ x₂ : ℝ} (hg₂ : g₂ x₁ x₂ ≠ 0)
    (hW₁ : dV₁ x₁ * (f₁ x₁ + g₁ x₁ * α₁ x₁) ≤ -W₁ x₁) :
    let u := backsteppingControl dV₁ f₁ g₁ α₁ dα₁ f₂ g₂ c₂ x₁ x₂
    dV₁ x₁ * (f₁ x₁ + g₁ x₁ * x₂) +
      (x₂ - α₁ x₁) * (f₂ x₁ x₂ + g₂ x₁ x₂ * u - dα₁ x₁ * (f₁ x₁ + g₁ x₁ * x₂)) ≤
    -W₁ x₁ - c₂ * (x₂ - α₁ x₁) ^ 2 := by
  intro u
  have h_eq := backstepping_closedLoop_lie_deriv dV₁ f₁ g₁ α₁ dα₁ f₂ g₂ c₂ x₁ x₂ hg₂
  dsimp at h_eq
  linarith

/-- **Strict Negative Definiteness of the Closed-Loop Backstepping Lie Derivative**:
If $\alpha_1(0) = 0$, $W_1(0) = 0$, $W_1(x_1) > 0$ for all $x_1 \ne 0$, and $c_2 > 0$, then
for every nonzero state $(x_1, x_2) \ne (0, 0)$,
$$-W_1(x_1) - c_2 (x_2 - \alpha_1(x_1))^2 < 0.$$ -/
theorem backstepping_strict_negDef {W₁ α₁ : ℝ → ℝ} {c₂ : ℝ}
    (hα₁0 : α₁ 0 = 0) (hW₁0 : W₁ 0 = 0)
    (hW₁_pos : ∀ x₁ ≠ 0, 0 < W₁ x₁) (hc₂ : 0 < c₂)
    {x₁ x₂ : ℝ} (hne : x₁ ≠ 0 ∨ x₂ ≠ 0) :
    -W₁ x₁ - c₂ * (x₂ - α₁ x₁) ^ 2 < 0 := by
  rcases eq_or_ne x₁ 0 with rfl | hx₁
  · rcases hne with h1 | hx₂
    · exact (h1 rfl).elim
    · rw [hW₁0, hα₁0, neg_zero, zero_sub, sub_zero]
      have : 0 < c₂ * x₂ ^ 2 := mul_pos hc₂ (sq_pos_of_ne_zero hx₂)
      linarith
  · have h1 : 0 < W₁ x₁ := hW₁_pos x₁ hx₁
    have h2 : 0 ≤ c₂ * (x₂ - α₁ x₁) ^ 2 := mul_nonneg hc₂.le (sq_nonneg _)
    linarith

/-! ### 2. Recursive $n$-Step Strict-Feedback Backstepping in Error Coordinates -/

/-- **Inductive Step of $n$-Integrator Backstepping in Error Coordinates**:
In skew-coupled error coordinates where stage $k$ has residual coupling $z_{k-1} g_{k-1} z_k$
and the error dynamics at stage $k$ are chosen as
$\dot{z}_k = -g_{k-1} z_{k-1} - c_k z_k + g_k z_{k+1}$, adding $z_k \dot{z}_k$ cancels
$z_{k-1} g_{k-1} z_k$ and advances the residual coupling to stage $k + 1$:
$$\left(-S + z_{k-1} g_{k-1} z_k\right) + z_k (-g_{k-1} z_{k-1} - c_k z_k + g_k z_{k+1})
  = -(S + c_k z_k^2) + z_k g_k z_{k+1}.$$ -/
theorem backstepping_step_dissipation (S z_prev g_prev z_curr c_curr g_curr z_next : ℝ) :
    (-S + z_prev * g_prev * z_curr) +
      z_curr * (-g_prev * z_prev - c_curr * z_curr + g_curr * z_next) =
    -(S + c_curr * z_curr ^ 2) + z_curr * g_curr * z_next := by
  ring

/-- **Telescoping Skew-Symmetric Cancellation across an $n$-Step Backstepping Chain**:
For any horizon $N$, error vector $z : \mathbb{N} \to \mathbb{R}$, gain vector
$c : \mathbb{N} \to \mathbb{R}$, and interconnection gains $g : \mathbb{N} \to \mathbb{R}$
with $z_0$ having no predecessor ($g_0^{\text{prev}} = 0$):
$$\sum_{k=0}^{N-1} z_k \bigl(-g_k z_{k-1} - c_k z_k + g_{k+1} z_{k+1}\bigr)
  = -\sum_{k=0}^{N-1} c_k z_k^2 - g_0 z_{-1} z_0 + g_N z_{N-1} z_N.$$ -/
theorem backstepping_chain_telescoping (z c g : ℕ → ℝ) :
    ∀ N : ℕ,
      ∑ k ∈ Finset.range N,
        z (k + 1) * (-g k * z k - c (k + 1) * z (k + 1) + g (k + 1) * z (k + 2)) =
      -(∑ k ∈ Finset.range N, c (k + 1) * z (k + 1) ^ 2) -
        g 0 * z 0 * z 1 + g N * z N * z (N + 1)
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, backstepping_chain_telescoping z c g N]
    ring

/-- **Closed-Loop $n$-Step Backstepping Dissipation Identity**:
When $z_0 = 0$ (no upstream coupling at the first integrator) and $z_{N+1} = 0$ (actual control
input $u$ cancels the final virtual error at stage $N$), the skew-symmetric tridiagonal
interconnection terms telescope to zero:
$$\sum_{k=0}^{N-1} z_{k+1} \bigl(-g_k z_k - c_{k+1} z_{k+1} + g_{k+1} z_{k+2}\bigr)
  = -\sum_{k=0}^{N-1} c_{k+1} z_{k+1}^2.$$ -/
theorem backstepping_chain_dissipation (z c g : ℕ → ℝ) (N : ℕ)
    (hz₀ : z 0 = 0) (hzN : z (N + 1) = 0) :
    ∑ k ∈ Finset.range N,
      z (k + 1) * (-g k * z k - c (k + 1) * z (k + 1) + g (k + 1) * z (k + 2)) =
    -(∑ k ∈ Finset.range N, c (k + 1) * z (k + 1) ^ 2) := by
  rw [backstepping_chain_telescoping z c g N, hz₀, hzN]
  ring

/-- **Genuine `HasDerivAt` for the $n$-Step Composite Backstepping Lyapunov Function**:
Along a differentiable error trajectory $z : \mathbb{R} \to \mathbb{N} \to \mathbb{R}$ satisfying
$\dot{z}_{k+1}(t) = -g_k z_k(t) - c_{k+1} z_{k+1}(t) + g_{k+1} z_{k+2}(t)$ with boundary
conditions $z_0(t) = 0$ and $z_{N+1}(t) = 0$, the composite quadratic Lyapunov function
$V(t) = \frac{1}{2} \sum_{k=0}^{N-1} z_{k+1}(t)^2$ has time derivative
$$\dot{V}(t) = -\sum_{k=0}^{N-1} c_{k+1} z_{k+1}(t)^2.$$ -/
theorem hasDerivAt_backstepping_chain (z : ℝ → ℕ → ℝ) (c g : ℕ → ℝ) (N : ℕ) (t : ℝ)
    (hz₀ : z t 0 = 0) (hzN : z t (N + 1) = 0)
    (hderiv : ∀ k ∈ Finset.range N,
      HasDerivAt (fun s => z s (k + 1))
        (-g k * z t k - c (k + 1) * z t (k + 1) + g (k + 1) * z t (k + 2)) t) :
    HasDerivAt (fun s => ∑ k ∈ Finset.range N, (1 / 2 : ℝ) * (z s (k + 1)) ^ 2)
      (-(∑ k ∈ Finset.range N, c (k + 1) * (z t (k + 1)) ^ 2)) t := by
  have hterm : ∀ k ∈ Finset.range N,
      HasDerivAt (fun s => (1 / 2 : ℝ) * (z s (k + 1)) ^ 2)
        (z t (k + 1) * (-g k * z t k - c (k + 1) * z t (k + 1) + g (k + 1) * z t (k + 2))) t := by
    intro k hk
    have hpow := ((hderiv k hk).pow 2).const_mul (1 / 2 : ℝ)
    refine hpow.congr_deriv ?_
    push_cast
    ring
  have hsum := HasDerivAt.sum hterm
  have hfun : (∑ k ∈ Finset.range N, fun s => (1 / 2 : ℝ) * (z s (k + 1)) ^ 2) =
      (fun s => ∑ k ∈ Finset.range N, (1 / 2 : ℝ) * (z s (k + 1)) ^ 2) := by
    ext s
    simp
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  exact backstepping_chain_dissipation (z t) c g N hz₀ hzN

/-! ### 3. Sontag's Universal Control Lyapunov Function (CLF) Formula -/

/-- **Sontag's Universal Stabilizing Feedback Formula** (Sontag 1989):
For a control-affine system $\dot{x} = f(x) + g(x) u$ with Lie derivatives
$a = L_f V(x)$ and $b = L_g V(x)$:
$$u_{\text{Sontag}}(a, b) = \begin{cases} 0 & \text{if } b = 0, \\
  -\dfrac{a + \sqrt{a^2 + b^4}}{b} & \text{if } b \ne 0. \end{cases}$$ -/
noncomputable def sontagControl (a b : ℝ) : ℝ :=
  if b = 0 then 0 else -(a + Real.sqrt (a ^ 2 + b ^ 4)) / b

/-- **Sontag's Universal Stabilizer Identity (`sontag_universal_stabilizer`)**:
Whenever the control Lie derivative is nonzero ($b \ne 0$), Sontag's feedback law yields the
exact closed-loop Lie derivative $-\sqrt{a^2 + b^4} < 0$:
$$a + b \cdot u_{\text{Sontag}}(a, b) = -\sqrt{a^2 + b^4} \quad \text{and} \quad
  a + b \cdot u_{\text{Sontag}}(a, b) < 0.$$ -/
theorem sontag_universal_stabilizer (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    a + b * sontagControl a b = -Real.sqrt (a ^ 2 + b ^ 4) ∧
      a + b * sontagControl a b < 0 := by
  have h_eq : a + b * sontagControl a b = -Real.sqrt (a ^ 2 + b ^ 4) := by
    unfold sontagControl
    simp only [hb, ↓reduceIte]
    field_simp [hb]
    ring
  refine ⟨h_eq, ?_⟩
  rw [h_eq, neg_lt_zero]
  refine Real.sqrt_pos.2 ?_
  have hb4 : 0 < b ^ 4 := by positivity
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  linarith

/-- **Artstein–Sontag Theorem (`sontag_clf_strict_decrease`)**:
If $(a, b) = (L_f V(x), L_g V(x))$ satisfies the Control Lyapunov Function (CLF) condition
($b = 0 \implies a < 0$), then Sontag's universal formula makes the closed-loop Lie derivative
strictly negative whether $b = 0$ or $b \ne 0$:
$$a + b \cdot u_{\text{Sontag}}(a, b) < 0.$$ -/
theorem sontag_clf_strict_decrease (a b : ℝ) (hclf : b = 0 → a < 0) :
    a + b * sontagControl a b < 0 := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp [sontagControl, hclf rfl]
  · exact (sontag_universal_stabilizer a hb).2

/-- **Genuine `HasDerivAt` for Sontag's Universal CLF Feedback**:
Along any differentiable scalar or vector trajectory where $s \mapsto V(s)$ has instantaneous
closed-loop derivative $a + b \cdot u_{\text{Sontag}}(a, b)$ under the CLF condition
($b = 0 \implies a < 0$), the Lyapunov function strictly decreases at time $t$. -/
theorem hasDerivAt_sontag_clf {V : ℝ → ℝ} {a b t : ℝ}
    (hV : HasDerivAt V (a + b * sontagControl a b) t)
    (hclf : b = 0 → a < 0) :
    ∃ d < 0, HasDerivAt V d t :=
  ⟨a + b * sontagControl a b, sontag_clf_strict_decrease a b hclf, hV⟩

end ControlsLean.Controls
