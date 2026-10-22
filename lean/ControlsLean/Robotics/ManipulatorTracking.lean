/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Robotics.SE3Kinematics
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Slotine–Li Passivity-Based Manipulator Trajectory Tracking

This module formalizes the **Slotine–Li (1987) Passivity-Based Trajectory Tracking & Adaptive
Control** architecture for $n$-DOF Euler–Lagrange robot manipulators:
$$M(q)\ddot{q} + C(q, \dot{q})\dot{q} + g(q) = \tau.$$

Unlike computed-torque feedback linearization—which requires online inversion of the inertia
matrix $M(q)^{-1}$ and exact cancellation of nonlinear Coriolis forces—the Slotine–Li
architecture introduces a virtual reference velocity $\dot{q}_r = \dot{q}_d - \Lambda \tilde{q}$
and composite sliding vector $s = \dot{q} - \dot{q}_r = \dot{\tilde{q}} + \Lambda \tilde{q}$,
exploiting the physical skew-symmetry of $\dot{M}(q) - 2 C(q, \dot{q})$ to achieve global
Lyapunov stability without inverting $M(q)$.

## Main Results

1. **Sliding-Surface Kinematics (`trackingError`, `referenceVel`, `slidingError`)**:
   - `slidingError_eq_velError_add`: $s = \dot{q} - \dot{q}_r = (\dot{q} - \dot{q}_d) + \Lambda (q - q_d)$.
   - `velError_eq_slidingError_sub`: $\dot{\tilde{q}} = s - \Lambda \tilde{q}$.

2. **Closed-Loop Slotine–Li Error Dynamics**:
   - `slotine_li_closed_loop_sliding`: Under $\tau = M \ddot{q}_r + C \dot{q}_r + g - K_D s$
     and $\ddot{q} - \ddot{q}_r = \dot{s}$, the manipulator dynamics reduce to
     $M \dot{s} + C s + K_D s = 0$.
   - `slotine_li_augmented_closed_loop`: Under $\tau = M \ddot{q}_r + C \dot{q}_r + g - K_D s - K_P \tilde{q}$,
     the closed-loop dynamics satisfy $M \dot{s} + C s + K_D s + K_P \tilde{q} = 0$.

3. **Passivity & Lyapunov Derivative Identities**:
   - `skew_coriolis_power_cancel`: $(\dot{M} - 2C)^\top = -(\dot{M} - 2C)$ implies
     $\frac{1}{2} s^\top \dot{M} s = s^\top C s$.
   - `slotine_li_lyapunov_deriv`: Along $M \dot{s} + C s + K_D s = 0$, the kinetic sliding
     storage derivative satisfies $\frac{1}{2} s^\top \dot{M} s + s^\top M \dot{s} = -s^\top K_D s$.
   - `slotine_li_augmented_lyapunov_deriv`: Along $M \dot{s} + C s + K_D s + K_P \tilde{q} = 0$
     with symmetric $K_P^\top = K_P$ and $\dot{\tilde{q}} = s - \Lambda \tilde{q}$, the cross terms
     $\pm s^\top K_P \tilde{q}$ cancel identically, yielding:
     $$\frac{1}{2} s^\top \dot{M} s + s^\top M \dot{s} + \tilde{q}^\top K_P \dot{\tilde{q}}
       = -s^\top K_D s - \tilde{q}^\top (K_P \Lambda) \tilde{q}.$$
   - `slotine_li_adaptive_lyapunov_deriv`: Under regressor parameterization
     $M \dot{s} + C s + K_D s = Y \tilde{\theta}$ and Slotine–Li adaptation law
     $\Gamma^{-1} \dot{\tilde{\theta}} = -Y^\top s$, the parameter-estimation power cancels
     identically:
     $$\frac{1}{2} s^\top \dot{M} s + s^\top M \dot{s} + \tilde{\theta}^\top (\Gamma^{-1} \dot{\tilde{\theta}})
       = -s^\top K_D s.$$

4. **Trajectory Calculus & Exponential Sliding-Surface Decay**:
   - `slotine_li_exponential_rate`: If $K_D$ dominates $\lambda M$ ($s^\top K_D s \ge \lambda s^\top M s$),
     then $\dot{V}_s \le -2 \lambda V_s(s)$ where $V_s(s) = \frac{1}{2} s^\top M s$.
   - `hasDerivAt_slotine_li_storage`: `HasDerivAt` certificate for the time-varying kinetic
     storage trajectory $V_s(t)$ and its exponentially weighted counterpart $e^{2\lambda t} V_s(t)$.
-/

namespace ControlsLean.Robotics

open Matrix Finset ControlsLean.Tactics

variable {n : Type*} [Fintype n]

/-! ## 1. Joint-Space Tracking Error & Sliding-Surface Kinematics -/

/-- Joint position tracking error $\tilde{q} = q - q_d$. -/
def trackingError (q q_d : n → ℝ) : n → ℝ :=
  q - q_d

/-- Slotine–Li virtual reference velocity $\dot{q}_r = \dot{q}_d - \Lambda \tilde{q}$. -/
def referenceVel (qdot_d : n → ℝ) (Λ : Matrix n n ℝ) (q_tilde : n → ℝ) : n → ℝ :=
  qdot_d - Λ *ᵥ q_tilde

/-- Composite sliding/reference velocity error $s = \dot{q} - \dot{q}_r$. -/
def slidingError (qdot qdot_r : n → ℝ) : n → ℝ :=
  qdot - qdot_r

/-- Kinematic equivalence: $s = \dot{q} - (\dot{q}_d - \Lambda (q - q_d)) = (\dot{q} - \dot{q}_d) + \Lambda (q - q_d)$. -/
theorem slidingError_eq_velError_add (q q_d qdot qdot_d : n → ℝ) (Λ : Matrix n n ℝ) :
    slidingError qdot (referenceVel qdot_d Λ (trackingError q q_d)) =
      (qdot - qdot_d) + Λ *ᵥ trackingError q q_d := by
  unfold slidingError referenceVel
  ext i
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

/-- Velocity tracking error recovery from the sliding vector:
$\dot{\tilde{q}} = s - \Lambda \tilde{q}$. -/
theorem velError_eq_slidingError_sub (q q_d qdot qdot_d : n → ℝ) (Λ : Matrix n n ℝ) :
    qdot - qdot_d =
      slidingError qdot (referenceVel qdot_d Λ (trackingError q q_d)) -
        Λ *ᵥ trackingError q q_d := by
  rw [slidingError_eq_velError_add, add_sub_cancel_right]

/-! ## 2. Closed-Loop Slotine–Li Manipulator Error Dynamics -/

/-- The Slotine–Li passivity-based control law:
$\tau = M \ddot{q}_r + C \dot{q}_r + g - K_D s$. -/
def slotineLiControl (M C Kd : Matrix n n ℝ) (qdot_r qddot_r g s : n → ℝ) : n → ℝ :=
  M *ᵥ qddot_r + C *ᵥ qdot_r + g - Kd *ᵥ s

/-- The augmented Slotine–Li control law with explicit position-error stiffness $K_P$:
$\tau = M \ddot{q}_r + C \dot{q}_r + g - K_D s - K_P \tilde{q}$. -/
def slotineLiAugmentedControl (M C Kd Kp : Matrix n n ℝ)
    (qdot_r qddot_r g s q_tilde : n → ℝ) : n → ℝ :=
  M *ᵥ qddot_r + C *ᵥ qdot_r + g - Kd *ᵥ s - Kp *ᵥ q_tilde

/-- **Closed-Loop Sliding Error Dynamics**:
For a manipulator $M \ddot{q} + C \dot{q} + g = \tau$ with $\dot{s} = \ddot{q} - \ddot{q}_r$
and $s = \dot{q} - \dot{q}_r$, applying `slotineLiControl` yields the homogeneous passivity
error equation $M \dot{s} + C s + K_D s = 0$. -/
theorem slotine_li_closed_loop_sliding
    (M C Kd : Matrix n n ℝ) (qdot qddot qdot_r qddot_r g s sdot τ : n → ℝ)
    (hs : s = qdot - qdot_r)
    (hsdot : sdot = qddot - qddot_r)
    (hdyn : M *ᵥ qddot + C *ᵥ qdot + g = τ)
    (hctrl : τ = slotineLiControl M C Kd qdot_r qddot_r g s) :
    M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s = 0 := by
  unfold slotineLiControl at hctrl
  have hCs : C *ᵥ s = C *ᵥ qdot - C *ᵥ qdot_r := by rw [hs, Matrix.mulVec_sub]
  rw [hsdot, Matrix.mulVec_sub, hCs]
  ext i
  have h_i := congr_fun (hdyn.trans hctrl) i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at h_i ⊢
  linarith

/-- **Closed-Loop Augmented Slotine–Li Error Dynamics**:
Under `slotineLiAugmentedControl`, the closed-loop error dynamics satisfy
$M \dot{s} + C s + K_D s + K_P \tilde{q} = 0$. -/
theorem slotine_li_augmented_closed_loop
    (M C Kd Kp : Matrix n n ℝ) (qdot qddot qdot_r qddot_r g s sdot q_tilde τ : n → ℝ)
    (hs : s = qdot - qdot_r)
    (hsdot : sdot = qddot - qddot_r)
    (hdyn : M *ᵥ qddot + C *ᵥ qdot + g = τ)
    (hctrl : τ = slotineLiAugmentedControl M C Kd Kp qdot_r qddot_r g s q_tilde) :
    M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s + Kp *ᵥ q_tilde = 0 := by
  unfold slotineLiAugmentedControl at hctrl
  have hCs : C *ᵥ s = C *ᵥ qdot - C *ᵥ qdot_r := by rw [hs, Matrix.mulVec_sub]
  rw [hsdot, Matrix.mulVec_sub, hCs]
  ext i
  have h_i := congr_fun (hdyn.trans hctrl) i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at h_i ⊢
  linarith

/-! ## 3. Skew-Symmetric Coriolis Cancellation & Lyapunov Derivative Identities -/

/-- **Physical Skew-Symmetry Power Cancellation**:
When $N = \dot{M} - 2 C$ is skew-symmetric ($N^\top = -N$), the Coriolis quadratic form
equals half the inertia-rate quadratic form:
$\frac{1}{2} s^\top \dot{M} s = s^\top C s$. -/
theorem skew_coriolis_power_cancel
    (Mdot C : Matrix n n ℝ) (s : n → ℝ)
    (hskew : (Mdot - (2 : ℝ) • C)ᵀ = -(Mdot - (2 : ℝ) • C)) :
    (1 / 2 : ℝ) * quad Mdot s = quad C s := by
  have hN0 : quad (Mdot - (2 : ℝ) • C) s = 0 := quad_skew (Mdot - (2 : ℝ) • C) hskew s
  have hquad_sub : quad (Mdot - (2 : ℝ) • C) s = quad Mdot s - 2 * quad C s := by
    simp [quad, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  linarith

/-- **Slotine–Li Sliding-Mode Lyapunov Derivative Identity**:
Along the closed-loop error dynamics $M \dot{s} + C s + K_D s = 0$ and under the skew-symmetry
property $(\dot{M} - 2 C)^\top = -(\dot{M} - 2 C)$, the time derivative of the kinetic sliding
storage function $V_s(s) = \frac{1}{2} s^\top M s$ is purely dissipative:
$$\frac{1}{2} s^\top \dot{M} s + s^\top (M \dot{s}) = -s^\top K_D s.$$ -/
theorem slotine_li_lyapunov_deriv
    (M Mdot C Kd : Matrix n n ℝ) (s sdot : n → ℝ)
    (hskew : (Mdot - (2 : ℝ) • C)ᵀ = -(Mdot - (2 : ℝ) • C))
    (hcl : M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s = 0) :
    (1 / 2 : ℝ) * quad Mdot s + s ⬝ᵥ (M *ᵥ sdot) = -quad Kd s := by
  have hcor := skew_coriolis_power_cancel Mdot C s hskew
  have hdot : s ⬝ᵥ (M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s) = 0 := by
    rw [hcl, dotProduct_zero]
  simp only [dotProduct_add, dotProduct_mulVec_eq_quad] at hdot
  linarith

/-- Non-positivity of the Slotine–Li Lyapunov derivative when $K_D$ is positive semidefinite. -/
theorem slotine_li_lyapunov_deriv_nonpos
    (M Mdot C Kd : Matrix n n ℝ) (s sdot : n → ℝ)
    (hskew : (Mdot - (2 : ℝ) • C)ᵀ = -(Mdot - (2 : ℝ) • C))
    (hcl : M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s = 0)
    (hKd : Kd.PosSemidef) :
    (1 / 2 : ℝ) * quad Mdot s + s ⬝ᵥ (M *ᵥ sdot) ≤ 0 := by
  rw [slotine_li_lyapunov_deriv M Mdot C Kd s sdot hskew hcl]
  have hpos := PosSemidef.quad_nonneg hKd s
  linarith

/-- Strict negativity of the Slotine–Li Lyapunov derivative for $s \ne 0$ when $K_D$ is
positive definite. -/
theorem slotine_li_lyapunov_deriv_neg
    (M Mdot C Kd : Matrix n n ℝ) (s sdot : n → ℝ)
    (hskew : (Mdot - (2 : ℝ) • C)ᵀ = -(Mdot - (2 : ℝ) • C))
    (hcl : M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s = 0)
    (hKd : Kd.PosDef) (hs : s ≠ 0) :
    (1 / 2 : ℝ) * quad Mdot s + s ⬝ᵥ (M *ᵥ sdot) < 0 := by
  rw [slotine_li_lyapunov_deriv M Mdot C Kd s sdot hskew hcl]
  have hpos := PosDef.quad_pos hKd hs
  linarith

/-- **Augmented Slotine–Li Joint-Space Storage Derivative**:
For the composite storage function $V(s, \tilde{q}) = \frac{1}{2} s^\top M s + \frac{1}{2} \tilde{q}^\top K_P \tilde{q}$
with symmetric $K_P^\top = K_P$, closed-loop dynamics $M \dot{s} + C s + K_D s + K_P \tilde{q} = 0$,
and sliding kinematic relation $\dot{\tilde{q}} = s - \Lambda \tilde{q}$, the cross terms
$\pm s^\top K_P \tilde{q}$ cancel identically, yielding strict joint-space dissipation in both
$s$ and $\tilde{q}$:
$$\frac{1}{2} s^\top \dot{M} s + s^\top (M \dot{s}) + \tilde{q}^\top (K_P \dot{\tilde{q}})
  = -s^\top K_D s - \tilde{q}^\top (K_P \Lambda) \tilde{q}.$$ -/
theorem slotine_li_augmented_lyapunov_deriv
    (M Mdot C Kd Kp Λ : Matrix n n ℝ) (s sdot q_tilde qdot_tilde : n → ℝ)
    (hskew : (Mdot - (2 : ℝ) • C)ᵀ = -(Mdot - (2 : ℝ) • C))
    (hKp_symm : Kpᵀ = Kp)
    (hcl : M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s + Kp *ᵥ q_tilde = 0)
    (hqdot : qdot_tilde = s - Λ *ᵥ q_tilde) :
    (1 / 2 : ℝ) * quad Mdot s + s ⬝ᵥ (M *ᵥ sdot) + q_tilde ⬝ᵥ (Kp *ᵥ qdot_tilde) =
      -quad Kd s - quad (Kp * Λ) q_tilde := by
  have hcor := skew_coriolis_power_cancel Mdot C s hskew
  have hdot : s ⬝ᵥ (M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s + Kp *ᵥ q_tilde) = 0 := by
    rw [hcl, dotProduct_zero]
  simp only [dotProduct_add, dotProduct_mulVec_eq_quad] at hdot
  have hcross : q_tilde ⬝ᵥ (Kp *ᵥ s) = s ⬝ᵥ (Kp *ᵥ q_tilde) := by
    calc q_tilde ⬝ᵥ (Kp *ᵥ s) = s ⬝ᵥ (Kpᵀ *ᵥ q_tilde) :=
          (dotProduct_transpose_mulVec Kp s q_tilde).symm
      _ = s ⬝ᵥ (Kp *ᵥ q_tilde) := by rw [hKp_symm]
  have hq_term : q_tilde ⬝ᵥ (Kp *ᵥ qdot_tilde) =
      s ⬝ᵥ (Kp *ᵥ q_tilde) - quad (Kp * Λ) q_tilde := by
    rw [hqdot, Matrix.mulVec_sub, dotProduct_sub, hcross, Matrix.mulVec_mulVec]
    rfl
  linarith

/-- **Adaptive Slotine–Li Parameter-Estimation Passivity Identity**:
When manipulator uncertainties are linearly parameterized via regressor matrix
$Y : \mathrm{Matrix}\ n\ p\ \mathbb{R}$ so that $M \dot{s} + C s + K_D s = Y \tilde{\theta}$,
and the parameter error $\tilde{\theta} = \hat{\theta} - \theta$ evolves under the Slotine–Li
adaptation law $\Gamma^{-1} \dot{\tilde{\theta}} = -Y^\top s$, the parameter error power cancels
the regressor mismatch power identically:
$$\frac{1}{2} s^\top \dot{M} s + s^\top (M \dot{s}) + \tilde{\theta}^\top (\Gamma^{-1} \dot{\tilde{\theta}})
  = -s^\top K_D s.$$ -/
theorem slotine_li_adaptive_lyapunov_deriv {p : Type*} [Fintype p]
    (M Mdot C Kd : Matrix n n ℝ) (Y : Matrix n p ℝ) (Γ_inv : Matrix p p ℝ)
    (s sdot : n → ℝ) (θ_tilde θdot_tilde : p → ℝ)
    (hskew : (Mdot - (2 : ℝ) • C)ᵀ = -(Mdot - (2 : ℝ) • C))
    (hcl : M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s = Y *ᵥ θ_tilde)
    (hadapt : Γ_inv *ᵥ θdot_tilde = -(Yᵀ *ᵥ s)) :
    (1 / 2 : ℝ) * quad Mdot s + s ⬝ᵥ (M *ᵥ sdot) + θ_tilde ⬝ᵥ (Γ_inv *ᵥ θdot_tilde) =
      -quad Kd s := by
  have hcor := skew_coriolis_power_cancel Mdot C s hskew
  have hdot : s ⬝ᵥ (M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s) = s ⬝ᵥ (Y *ᵥ θ_tilde) := by
    rw [hcl]
  simp only [dotProduct_add, dotProduct_mulVec_eq_quad] at hdot
  have hadapt_dot : θ_tilde ⬝ᵥ (Γ_inv *ᵥ θdot_tilde) = -(s ⬝ᵥ (Y *ᵥ θ_tilde)) := by
    rw [hadapt, dotProduct_neg, dotProduct_transpose_mulVec]
  linarith

/-! ## 4. Exponential Sliding-Surface Decay & Trajectory Calculus -/

/-- **Exponential Sliding-Surface Decay Rate**:
If the damping matrix $K_D$ dominates $\lambda M$ ($s^\top K_D s \ge \lambda s^\top M s$), then the
Slotine–Li Lyapunov derivative satisfies
$$\frac{1}{2} s^\top \dot{M} s + s^\top (M \dot{s}) \le -2 \lambda \left(\frac{1}{2} s^\top M s\right).$$ -/
theorem slotine_li_exponential_rate
    (M Mdot C Kd : Matrix n n ℝ) (s sdot : n → ℝ) (lam : ℝ)
    (hskew : (Mdot - (2 : ℝ) • C)ᵀ = -(Mdot - (2 : ℝ) • C))
    (hcl : M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s = 0)
    (hdom : lam * quad M s ≤ quad Kd s) :
    (1 / 2 : ℝ) * quad Mdot s + s ⬝ᵥ (M *ᵥ sdot) ≤
      -2 * lam * ((1 / 2 : ℝ) * quad M s) := by
  rw [slotine_li_lyapunov_deriv M Mdot C Kd s sdot hskew hcl]
  linarith

/-- **Trajectory Calculus Certificate for Slotine–Li Exponential Storage Decay**:
If the kinetic sliding storage trajectory $V_s : \mathbb{R} \to \mathbb{R}$ has derivative
$\dot{V}_s(t) = \frac{1}{2} s(t)^\top \dot{M}(t) s(t) + s(t)^\top M(t) \dot{s}(t)$ at time $t$,
then under the Slotine–Li closed-loop dynamics and damping dominance
$s(t)^\top K_D s(t) \ge \lambda s(t)^\top M(t) s(t)$, the exponentially scaled storage function
$W(t) = e^{2\lambda t} V_s(t)$ has non-positive time derivative $\dot{W}(t) \le 0$. -/
theorem hasDerivAt_slotine_li_storage
    (V_s : ℝ → ℝ) (M Mdot C Kd : Matrix n n ℝ) (s sdot : n → ℝ) (lam t : ℝ)
    (hV_val : V_s t = (1 / 2 : ℝ) * quad M s)
    (hV_deriv : HasDerivAt V_s ((1 / 2 : ℝ) * quad Mdot s + s ⬝ᵥ (M *ᵥ sdot)) t)
    (hskew : (Mdot - (2 : ℝ) • C)ᵀ = -(Mdot - (2 : ℝ) • C))
    (hcl : M *ᵥ sdot + C *ᵥ s + Kd *ᵥ s = 0)
    (hdom : lam * quad M s ≤ quad Kd s) :
    ∃ dW : ℝ,
      HasDerivAt (fun τ ↦ Real.exp (2 * lam * τ) * V_s τ) dW t ∧ dW ≤ 0 := by
  have hexp : HasDerivAt (fun τ ↦ Real.exp (2 * lam * τ))
      (Real.exp (2 * lam * t) * (2 * lam)) t := by
    have hlin : HasDerivAt (fun τ : ℝ ↦ 2 * lam * τ) (2 * lam) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * lam)
    exact hlin.exp
  have hW := hexp.mul hV_deriv
  refine ⟨Real.exp (2 * lam * t) * (2 * lam) * V_s t +
    Real.exp (2 * lam * t) * ((1 / 2 : ℝ) * quad Mdot s + s ⬝ᵥ (M *ᵥ sdot)), hW, ?_⟩
  have hrate := slotine_li_exponential_rate M Mdot C Kd s sdot lam hskew hcl hdom
  rw [hV_val]
  have hexp_pos : 0 < Real.exp (2 * lam * t) := Real.exp_pos _
  nlinarith

end ControlsLean.Robotics
