/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Robotics.SO3Rodrigues
import ControlsLean.Tactics.ControlTactics

/-!
# $\mathrm{SE}(3)$ Spatial Kinematics, Adjoint Map & Manipulator Passivity

This module formalizes:
1. **3D Rigid-Body Transformations** on $\mathrm{SE}(3)$ and the $6 \times 6$ spatial Adjoint
   matrix $\mathrm{Ad}_{(R, p)} = \begin{bmatrix} R & 0 \\ [p]_× R & R \end{bmatrix}$:
   - `adjoint6_one`: $\mathrm{Ad}_{(I, 0)} = I_6$.
   - `adjoint6_mul`: Equivariance $[p_1 + R_1 p_2]_× = [p_1]_× + R_1 [p_2]_× R_1^\top$ for
     $R_1 \in \mathrm{SO}(3)$ implies the group homomorphism law
     $\mathrm{Ad}_{(R_1, p_1)(R_2, p_2)} = \mathrm{Ad}_{(R_1, p_1)} \mathrm{Ad}_{(R_2, p_2)}$.
   - `adjoint6_inv_mul`: $\mathrm{Ad}_{(R^\top, -R^\top p)} \mathrm{Ad}_{(R, p)} = I_6$.
   - `det_adjoint6`: $\det(\mathrm{Ad}_{(R, p)}) = (\det R)^2$.
   - `wrench_twist_power_invariance`: Spatial wrench–twist power pairing
     $\mathcal{F}^\top \mathcal{V}$ is invariant under $\mathrm{SE}(3)$ frame transformations:
     $(\mathrm{Ad}_g^{-\top} \mathcal{F}) \cdot (\mathrm{Ad}_g \mathcal{V})
     = \mathcal{F} \cdot \mathcal{V}$.
2. **Euler–Lagrange Manipulator Passivity & PD+Gravity Control**:
   - `manipulator_passivity_power`: Under the skew-symmetric structural property
     $(\dot{M} - 2C)^\top = -(\dot{M} - 2C)$, the kinetic energy derivative satisfies
     $\frac{1}{2} \dot{q}^\top \dot{M} \dot{q} + \dot{q}^\top (M \ddot{q} + C \dot{q} + g)
     = \dot{q}^\top \tau$.
   - `manipulator_pd_gravity_lyapunov`: Under PD+gravity feedback
     $\tau = g(q) - K_p e - K_d \dot{q}$, the closed-loop storage derivative equals the negative
     rayleigh dissipation $-\dot{q}^\top K_d \dot{q} \le 0$.
-/

namespace ControlsLean.Robotics

open Matrix Finset ControlsLean.Vision ControlsLean.Tactics

/-- The $6 \times 6$ spatial Adjoint matrix of a rigid transformation $(R, p)$:
$\mathrm{Ad}_{(R, p)} = \begin{bmatrix} R & 0 \\ [p]_× R & R \end{bmatrix}$
mapping spatial twists $\mathcal{V} = (\omega, v) \in \mathbb{R}^3 \oplus \mathbb{R}^3$. -/
def adjoint6 {S : Type*} [Field S] (R : Matrix (Fin 3) (Fin 3) S) (p : Fin 3 → S) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) S :=
  fromBlocks R 0 (skew p * R) R

/-- Identity rigid transformation yields the $6 \times 6$ identity Adjoint matrix. -/
theorem adjoint6_one {S : Type*} [Field S] :
    adjoint6 (1 : Matrix (Fin 3) (Fin 3) S) (0 : Fin 3 → S) = 1 := by
  have hskew0 : skew (0 : Fin 3 → S) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skew]
  simp [adjoint6, hskew0, fromBlocks_one]

/-- Skew-matrix addition linearity: $[u + v]_× = [u]_× + [v]_×$. -/
theorem skew_add {S : Type*} [Field S] (u v : Fin 3 → S) :
    skew (u + v) = skew u + skew v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew] <;> ring

/-- Skew-matrix negation: $[-u]_× = -[u]_×$. -/
theorem skew_neg {S : Type*} [Field S] (u : Fin 3 → S) :
    skew (-u) = -skew u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew]

/-- **$\mathrm{SE}(3)$ Spatial Adjoint Homomorphism**:
Whenever $R_1 [p_2]_× R_1^\top = [R_1 p_2]_×$ (which holds for every $R_1 \in \mathrm{SO}(3)$),
$\mathrm{Ad}_{(R_1 R_2,\, p_1 + R_1 p_2)} = \mathrm{Ad}_{(R_1, p_1)} \mathrm{Ad}_{(R_2, p_2)}$. -/
theorem adjoint6_mul {S : Type*} [Field S]
    (R₁ R₂ : Matrix (Fin 3) (Fin 3) S) (p₁ p₂ : Fin 3 → S)
    (hequiv : skew (R₁ *ᵥ p₂) * R₁ = R₁ * skew p₂) :
    adjoint6 (R₁ * R₂) (p₁ + R₁ *ᵥ p₂) = adjoint6 R₁ p₁ * adjoint6 R₂ p₂ := by
  dsimp [adjoint6]
  rw [fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  congr 1
  rw [skew_add, add_mul, ← Matrix.mul_assoc (skew (R₁ *ᵥ p₂)) R₁ R₂, hequiv]
  simp only [Matrix.mul_assoc]

/-- **$\mathrm{SE}(3)$ Spatial Adjoint Inverse**:
If $R^\top R = I_3$ and $R^\top [p]_× R = [R^\top p]_×$, then
$\mathrm{Ad}_{(R^\top, -R^\top p)} \mathrm{Ad}_{(R, p)} = I_6$. -/
theorem adjoint6_inv_mul {S : Type*} [Field S]
    (R : Matrix (Fin 3) (Fin 3) S) (p : Fin 3 → S)
    (hR : Rᵀ * R = 1)
    (hequiv : skew (Rᵀ *ᵥ p) * Rᵀ = Rᵀ * skew p) :
    adjoint6 Rᵀ (-(Rᵀ *ᵥ p)) * adjoint6 R p = 1 := by
  dsimp [adjoint6]
  rw [fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add, hR, skew_neg, neg_mul]
  have hcancel : -(skew (Rᵀ *ᵥ p) * Rᵀ * R) + Rᵀ * (skew p * R) = 0 := by
    rw [hequiv, Matrix.mul_assoc, neg_add_cancel]
  rw [hcancel, fromBlocks_one]

/-- **Determinant of the Spatial Adjoint**:
$\det(\mathrm{Ad}_{(R, p)}) = (\det R)^2$. In particular, $\det(\mathrm{Ad}_{(R, p)}) = 1$ for
every $R \in \mathrm{SO}(3)$ ($\det R = 1$). -/
theorem det_adjoint6 {S : Type*} [Field S]
    (R : Matrix (Fin 3) (Fin 3) S) (p : Fin 3 → S) :
    (adjoint6 R p).det = R.det ^ 2 := by
  dsimp [adjoint6]
  rw [det_fromBlocks_zero₁₂, sq]

/-- **Spatial Wrench–Twist Power Invariance**:
For any invertible spatial transformation $A$ with left inverse $B$ ($B A = I$),
the dual wrench transformation $B^\top \mathcal{F}$ preserves instantaneous mechanical power:
$(B^\top \mathcal{F}) \cdot (A \mathcal{V}) = \mathcal{F} \cdot \mathcal{V}$. -/
theorem wrench_twist_power_invariance {n S : Type*} [Fintype n] [DecidableEq n] [CommRing S]
    (A B : Matrix n n S) (hBA : B * A = 1) (F V : n → S) :
    (Bᵀ *ᵥ F) ⬝ᵥ (A *ᵥ V) = F ⬝ᵥ V := by
  rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul, hBA, vecMul_one]

/-- **Euler–Lagrange Manipulator Passivity Identity**:
For a mechanical manipulator with dynamics $M \ddot{q} + C \dot{q} + g = \tau$ and
skew-symmetric structural matrix $N = \dot{M} - 2 C$ satisfying $N^\top = -N$, the rate of change
of kinetic + potential energy equals the external mechanical power $\dot{q} \cdot \tau$:
$\dot{q}^\top (M \ddot{q} + g) + \frac{1}{2} \dot{q}^\top \dot{M} \dot{q} = \dot{q}^\top \tau$. -/
theorem manipulator_passivity_power {n : Type*} [Fintype n] [DecidableEq n]
    (M Mdot C : Matrix n n ℝ) (qdot qddot g τ : n → ℝ)
    (hskew : (Mdot - (2 : ℝ) • C)ᵀ = -(Mdot - (2 : ℝ) • C))
    (hdyn : M *ᵥ qddot + C *ᵥ qdot + g = τ) :
    qdot ⬝ᵥ (M *ᵥ qddot + g) + (1 / 2 : ℝ) * quad Mdot qdot = qdot ⬝ᵥ τ := by
  have hN0 : quad (Mdot - (2 : ℝ) • C) qdot = 0 := quad_skew (Mdot - (2 : ℝ) • C) hskew qdot
  have hquad_sub : quad (Mdot - (2 : ℝ) • C) qdot = quad Mdot qdot - 2 * quad C qdot := by
    simp [quad, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hC : quad Mdot qdot = 2 * (qdot ⬝ᵥ (C *ᵥ qdot)) := by
    dsimp [quad] at hN0 hquad_sub ⊢
    linarith
  have hdot : qdot ⬝ᵥ (M *ᵥ qddot + C *ᵥ qdot + g) = qdot ⬝ᵥ τ := by rw [hdyn]
  simp only [dotProduct_add] at hdot ⊢
  dsimp [quad] at hC ⊢
  linarith

/-- **Manipulator PD + Gravity Control Energy Dissipation**:
Under PD + gravity compensation $\tau = g - K_p e - K_d \dot{q}$ alongside the skew-symmetry
condition $(\dot{M} - 2 C)^\top = -(\dot{M} - 2 C)$, the total mechanical power balance yields
$\dot{q}^\top (M \ddot{q} + K_p e) + \frac{1}{2} \dot{q}^\top \dot{M} \dot{q}
= -\dot{q}^\top K_d \dot{q}$. -/
theorem manipulator_pd_gravity_lyapunov {n : Type*} [Fintype n] [DecidableEq n]
    (M Mdot C Kp Kd : Matrix n n ℝ) (qdot qddot e g τ : n → ℝ)
    (hskew : (Mdot - (2 : ℝ) • C)ᵀ = -(Mdot - (2 : ℝ) • C))
    (hdyn : M *ᵥ qddot + C *ᵥ qdot + g = τ)
    (hctrl : τ = g - Kp *ᵥ e - Kd *ᵥ qdot) :
    qdot ⬝ᵥ (M *ᵥ qddot + Kp *ᵥ e) + (1 / 2 : ℝ) * quad Mdot qdot = -quad Kd qdot := by
  have hpass := manipulator_passivity_power M Mdot C qdot qddot g τ hskew hdyn
  rw [hctrl] at hpass
  simp only [quad, dotProduct_add, dotProduct_sub] at hpass ⊢
  linarith

end ControlsLean.Robotics
