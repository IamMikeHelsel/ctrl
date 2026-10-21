/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Vision.Epipolar
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# 3D Rotation Lie Algebra $\mathfrak{so}(3)$ & Rodrigues' Rotation Formula

This module formalizes the Lie-algebraic structure of 3D skew-symmetric matrices
$[ω]_× \in \mathfrak{so}(3)$ and **Rodrigues' rotation formula**:
$$R(\omega, \theta) = I + (\sin \theta) [\omega]_× + (1 - \cos \theta) [\omega]_×^2$$
for a unit rotation axis $\omega \in \mathbb{R}^3$ ($\omega \cdot \omega = 1$).

## Main results

- `skew_mulVec_self`: $[ω]_× \omega = 0$.
- `skew_sq`: $[ω]_×^2 = \omega \omega^\top - (\omega \cdot \omega) I_3$.
- `skew_cube`: Cayley–Hamilton identity $[ω]_×^3 = -(\omega \cdot \omega) [ω]_×$.
- `trace_skew`: $\operatorname{tr}([ω]_×) = 0$.
- `trace_skew_sq`: $\operatorname{tr}([ω]_×^2) = -2 (\omega \cdot \omega)$.
- `skew_lie_bracket`: Lie algebra homomorphism
  $[[u]_×, [v]_×] = [u \times_3 v]_×$.
- `rodrigues_transpose`: $R(\omega, \theta)^\top = R(\omega, -\theta)$.
- `rodrigues_mulVec_self`: Axis invariance $R(\omega, \theta) \omega = \omega$.
- `rodrigues_mul_rodrigues`: One-parameter subgroup composition
  $R(\omega, \alpha) R(\omega, \beta) = R(\omega, \alpha + \beta)$ for unit axis $\omega$.
- `rodrigues_transpose_mul_self` & `rodrigues_mul_transpose_self`: Orthogonality
  $R(\omega, \theta)^\top R(\omega, \theta) = I_3$ and
  $R(\omega, \theta) R(\omega, \theta)^\top = I_3$ on the unit sphere $\omega \cdot \omega = 1$.
- `trace_rodrigues`: Canonical trace formula
  $\operatorname{tr}(R(\omega, \theta)) = 1 + 2 \cos \theta$ for unit axis $\omega$.
-/

namespace ControlsLean.Robotics

open Matrix Finset ControlsLean.Vision

variable {K : Type*} [Field K]

/-- Self-annihilation of the hat matrix along its own axis: $[ω]_× \omega = 0$. -/
theorem skew_mulVec_self (ω : Fin 3 → K) : skew ω *ᵥ ω = 0 := by
  rw [skew_mulVec, cross_self]

/-- Explicit entries of $[ω]_×^2$:
$[ω]_×^2 = \omega \omega^\top - (\omega \cdot \omega) I_3$. -/
theorem skew_sq (ω : Fin 3 → K) :
    skew ω * skew ω = vecMulVec ω ω - (ω ⬝ᵥ ω) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew, Matrix.mul_apply, vecMulVec_apply, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- **Cayley–Hamilton identity on $\mathfrak{so}(3)$**:
$[ω]_×^3 = -(\omega \cdot \omega) [ω]_×$. -/
theorem skew_cube (ω : Fin 3 → K) :
    skew ω * (skew ω * skew ω) = -(ω ⬝ᵥ ω) • skew ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew, Matrix.mul_apply, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- Every skew-symmetric matrix $[ω]_×$ is trace-free: $\operatorname{tr}([ω]_×) = 0$. -/
theorem trace_skew (ω : Fin 3 → K) :
    (skew ω).trace = 0 := by
  rw [Matrix.trace, Fin.sum_univ_three]
  simp [Matrix.diag, skew]

/-- Trace of the squared hat matrix:
$\operatorname{tr}([ω]_×^2) = -2 (\omega \cdot \omega)$. -/
theorem trace_skew_sq (ω : Fin 3 → K) :
    (skew ω * skew ω).trace = -2 * (ω ⬝ᵥ ω) := by
  simp [Matrix.trace, Matrix.diag, skew, Matrix.mul_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- **Lie Algebra Homomorphism**: The matrix commutator of two hat matrices equals the hat matrix
of their 3D cross product:
$[u]_× [v]_× - [v]_× [u]_× = [u \times_3 v]_×$. -/
theorem skew_lie_bracket (u v : Fin 3 → K) :
    skew u * skew v - skew v * skew u = skew (u ⨯₃ v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew, cross_apply] <;>
    ring

/-- Transpose of the squared hat matrix: $([ω]_×^2)^\top = [ω]_×^2$. -/
theorem transpose_skew_sq (ω : Fin 3 → K) :
    (skew ω * skew ω)ᵀ = skew ω * skew ω := by
  rw [transpose_mul, skew_transpose, neg_mul_neg]

/-- **Rodrigues' Rotation Matrix**:
$R(\omega, \theta) = I_3 + (\sin \theta) [\omega]_× + (1 - \cos \theta) [\omega]_×^2$. -/
noncomputable def rodrigues (ω : Fin 3 → ℝ) (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 + Real.sin θ • skew ω + (1 - Real.cos θ) • (skew ω * skew ω)

/-- **Transpose Symmetry of Rodrigues' Formula**:
$R(\omega, \theta)^\top = R(\omega, -\theta)$. -/
theorem rodrigues_transpose (ω : Fin 3 → ℝ) (θ : ℝ) :
    (rodrigues ω θ)ᵀ = rodrigues ω (-θ) := by
  simp only [rodrigues, transpose_add, transpose_one, transpose_smul,
    skew_transpose, transpose_skew_sq, Real.sin_neg, Real.cos_neg, smul_neg, neg_smul]

/-- **Rotation Axis Invariance**: The rotation axis $\omega$ is a fixed point of
$R(\omega, \theta)$: $R(\omega, \theta) \omega = \omega$. -/
theorem rodrigues_mulVec_self (ω : Fin 3 → ℝ) (θ : ℝ) :
    rodrigues ω θ *ᵥ ω = ω := by
  simp only [rodrigues, add_mulVec, one_mulVec, smul_mulVec,
    ← mulVec_mulVec, skew_mulVec_self, mulVec_zero, smul_zero, add_zero]

/-- **One-Parameter Subgroup Composition on $\mathrm{SO}(3)$**:
For any unit vector $\omega \in \mathbb{R}^3$ ($\omega \cdot \omega = 1$),
$R(\omega, \alpha) R(\omega, \beta) = R(\omega, \alpha + \beta)$. -/
theorem rodrigues_mul_rodrigues (ω : Fin 3 → ℝ) (hω : ω ⬝ᵥ ω = 1) (α β : ℝ) :
    rodrigues ω α * rodrigues ω β = rodrigues ω (α + β) := by
  have h3 : skew ω * (skew ω * skew ω) = -skew ω := by
    rw [skew_cube, hω, neg_one_smul]
  have h3' : (skew ω * skew ω) * skew ω = -skew ω := by
    rw [Matrix.mul_assoc, h3]
  have h4 : (skew ω * skew ω) * (skew ω * skew ω) = -(skew ω * skew ω) := by
    calc (skew ω * skew ω) * (skew ω * skew ω)
        = skew ω * (skew ω * (skew ω * skew ω)) := by simp [Matrix.mul_assoc]
      _ = skew ω * (-skew ω) := by rw [h3]
      _ = -(skew ω * skew ω) := mul_neg (skew ω) (skew ω)
  have hsin : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β :=
    Real.sin_add α β
  have hcos : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β :=
    Real.cos_add α β
  ext i j
  simp only [rodrigues, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    h3, h3', h4, smul_neg, hsin, hcos]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- Evaluation at zero angle yields the identity matrix: $R(\omega, 0) = I_3$. -/
theorem rodrigues_zero (ω : Fin 3 → ℝ) : rodrigues ω 0 = 1 := by
  simp [rodrigues]

/-- **Left Orthogonality of Rodrigues' Rotation Matrix**:
For any unit vector $\omega \in \mathbb{R}^3$ ($\omega \cdot \omega = 1$),
$R(\omega, \theta)^\top R(\omega, \theta) = I_3$. -/
theorem rodrigues_transpose_mul_self (ω : Fin 3 → ℝ) (hω : ω ⬝ᵥ ω = 1) (θ : ℝ) :
    (rodrigues ω θ)ᵀ * rodrigues ω θ = 1 := by
  rw [rodrigues_transpose, rodrigues_mul_rodrigues ω hω (-θ) θ, neg_add_cancel, rodrigues_zero]

/-- **Right Orthogonality of Rodrigues' Rotation Matrix**:
For any unit vector $\omega \in \mathbb{R}^3$ ($\omega \cdot \omega = 1$),
$R(\omega, \theta) R(\omega, \theta)^\top = I_3$. -/
theorem rodrigues_mul_transpose_self (ω : Fin 3 → ℝ) (hω : ω ⬝ᵥ ω = 1) (θ : ℝ) :
    rodrigues ω θ * (rodrigues ω θ)ᵀ = 1 := by
  rw [rodrigues_transpose, rodrigues_mul_rodrigues ω hω θ (-θ), add_neg_cancel, rodrigues_zero]

/-- **Trace of Rodrigues' Rotation Matrix**:
For any unit vector $\omega \in \mathbb{R}^3$ ($\omega \cdot \omega = 1$),
$\operatorname{tr}(R(\omega, \theta)) = 1 + 2 \cos \theta$. -/
theorem trace_rodrigues (ω : Fin 3 → ℝ) (hω : ω ⬝ᵥ ω = 1) (θ : ℝ) :
    (rodrigues ω θ).trace = 1 + 2 * Real.cos θ := by
  simp only [rodrigues, trace_add, trace_smul, trace_skew, trace_skew_sq, hω,
    trace_one, Fintype.card_fin]
  norm_num
  ring

end ControlsLean.Robotics
