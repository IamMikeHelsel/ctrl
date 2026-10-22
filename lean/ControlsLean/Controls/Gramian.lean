/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ControlsLean.Controls.Reachability

/-!
# Discrete-Time Controllability Gramian and Minimum-Energy Steering

This module formalizes the discrete-time finite-horizon controllability Gramian
and exact minimum-energy state steering for linear time-invariant (LTI) systems
`x_{k+1} = A x_k + B u_k`, where `A` is an `n × n` matrix and `B` is an `n × m` matrix over `ℝ`.

## Main Definitions

* `ControlsLean.Controls.term A B i`:
  The `i`-th stage Gramian summand: `(A ^ i) * B * Bᵀ * ((A ^ i)ᵀ)`.
* `ControlsLean.Controls.gramian A B k`:
  The `k`-step controllability Gramian: `∑ i ∈ Finset.range k, term A B i`.
* `ControlsLean.Controls.steerControl A B k W_inv x₁ i`:
  The minimum-energy control input at stage `i < k` steering from `0` to `x₁`:
  `Bᵀ *ᵥ (((A ^ (k - 1 - i.val))ᵀ) *ᵥ (W_inv *ᵥ x₁))`.

## Headline Theorems

* `ControlsLean.Controls.term_transpose`:
  Each term is symmetric: `(term A B i)ᵀ = term A B i`.
* `ControlsLean.Controls.gramian_transpose`:
  The Gramian is symmetric: `(gramian A B k)ᵀ = gramian A B k`.
* `ControlsLean.Controls.quad_gramian_term`:
  The quadratic form of each stage summand satisfies:
  `x ⬝ᵥ (term A B i *ᵥ x) = ‖Bᵀ (A ^ i)ᵀ x‖²`.
* `ControlsLean.Controls.quad_gramian_term_nonneg`:
  Each summand is positive semidefinite: `0 ≤ x ⬝ᵥ (term A B i *ᵥ x)`.
* `ControlsLean.Controls.quad_gramian_nonneg`:
  The Gramian is positive semidefinite: `0 ≤ x ⬝ᵥ (gramian A B k *ᵥ x)`.
* `ControlsLean.Controls.gramian_steer`:
  **Kalman–Ho–Narendra Steering Theorem**: If `gramian A B k * W_inv = 1`,
  the control sequence `steerControl` steers the state from `0` to exactly `x₁` in `k` steps:
  `∑ i : Fin k, A ^ (k - 1 - i) *ᵥ (B *ᵥ steerControl A B k W_inv x₁ i) = x₁`.

## Literature References

* Kalman, R. E., Ho, Y. C., & Narendra, K. S. (1963). Controllability of Linear Dynamical Systems.
  *Contributions to Differential Equations*, 1(2): 189–213.
* Hespanha, J. P. (2018). *Linear Systems Theory* (2nd ed.). Princeton University Press.
  Chapter 10: "Controllability Gramian", Definition 10.1, Theorem 10.2 (pp. 115–122).
-/

namespace ControlsLean.Controls

open Matrix BigOperators

variable {n m : ℕ}

/-- The `i`-th stage Gramian summand: `Aⁱ B Bᵀ (Aⁱ)ᵀ`. -/
def term (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (i : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (A ^ i) * B * Bᵀ * ((A ^ i)ᵀ)

/-- The discrete-time finite-horizon controllability Gramian:
`W_k = ∑_{i=0}^{k-1} Aⁱ B Bᵀ (Aⁱ)ᵀ`. -/
def gramian (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ i ∈ Finset.range k, term A B i

/-- The minimum-energy steering control input at time index `i < k` to reach `x₁` from `0`
in `k` steps given a right-inverse `W_inv` of `gramian A B k`. -/
def steerControl (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (k : ℕ) (W_inv : Matrix (Fin n) (Fin n) ℝ) (x₁ : Fin n → ℝ) (i : Fin k) : Fin m → ℝ :=
  Bᵀ *ᵥ (((A ^ (k - 1 - (i : ℕ)))ᵀ) *ᵥ (W_inv *ᵥ x₁))

/-- Alias for `steerControl` matching optimal control terminology. -/
def steeringInput (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (k : ℕ) (W_inv : Matrix (Fin n) (Fin n) ℝ) (x₁ : Fin n → ℝ) (i : Fin k) : Fin m → ℝ :=
  steerControl A B k W_inv x₁ i

/-- Each Gramian summand is symmetric. -/
theorem term_transpose (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (i : ℕ) :
    (term A B i)ᵀ = term A B i := by
  unfold term
  simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]

/-- The controllability Gramian is symmetric: `W_kᵀ = W_k`. -/
theorem gramian_transpose (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (k : ℕ) :
    (gramian A B k)ᵀ = gramian A B k := by
  unfold gramian
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun i _ => term_transpose A B i

/-- Quadratic form of an individual Gramian summand:
`xᵀ (Aⁱ B Bᵀ (Aⁱ)ᵀ) x = ‖Bᵀ (Aⁱ)ᵀ x‖²`. -/
theorem quad_gramian_term (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (i : ℕ) (x : Fin n → ℝ) :
    x ⬝ᵥ (term A B i *ᵥ x) = (Bᵀ *ᵥ ((A ^ i)ᵀ *ᵥ x)) ⬝ᵥ (Bᵀ *ᵥ ((A ^ i)ᵀ *ᵥ x)) := by
  have hM : term A B i = ((A ^ i) * B) * ((A ^ i) * B)ᵀ := by
    unfold term
    simp only [transpose_mul, Matrix.mul_assoc]
  have h_vecMul : Bᵀ *ᵥ ((A ^ i)ᵀ *ᵥ x) = ((A ^ i) * B)ᵀ *ᵥ x := by
    rw [transpose_mul, ← mulVec_mulVec]
  rw [hM, h_vecMul, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

/-- Inner product of any real vector with itself is non-negative. -/
theorem dotProduct_self_nonneg (v : Fin m → ℝ) : 0 ≤ v ⬝ᵥ v := by
  unfold dotProduct
  apply Finset.sum_nonneg
  intro j _
  exact mul_self_nonneg (v j)

/-- Quadratic form of an individual Gramian summand is non-negative. -/
theorem quad_gramian_term_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (i : ℕ) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ (term A B i *ᵥ x) := by
  rw [quad_gramian_term]
  exact dotProduct_self_nonneg _

/-- The Gramian sum over `Finset.range k` equals the sum over the finite type `Fin k`. -/
theorem gramian_eq_sum_fin (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (k : ℕ) :
    gramian A B k = ∑ i : Fin k, term A B (i : ℕ) := by
  unfold gramian
  exact (Fin.sum_univ_eq_sum_range (fun i => term A B i) k).symm

/-- The controllability Gramian is positive semidefinite: `0 ≤ xᵀ W_k x`. -/
theorem quad_gramian_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (k : ℕ) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ (gramian A B k *ᵥ x) := by
  unfold gramian
  rw [sum_mulVec, dotProduct_sum]
  apply Finset.sum_nonneg
  intro i _
  exact quad_gramian_term_nonneg A B i x

/-- Base case: the 0-step Gramian is zero. -/
@[simp] theorem gramian_zero (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    gramian A B 0 = 0 := by
  unfold gramian
  simp

/-- Inductive step for the controllability Gramian: `W_{k+1} = W_k + term A B k`. -/
theorem gramian_succ (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (k : ℕ) :
    gramian A B (k + 1) = gramian A B k + term A B k := by
  unfold gramian
  rw [Finset.sum_range_succ]

/-- **Kalman–Ho–Narendra Steering Theorem**:
If `gramian A B k` has right-inverse `W_inv`, then the steering control input sequence
`steerControl` drives the system state from `0` to exactly `x₁` in `k` steps. -/
theorem gramian_steer (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (k : ℕ)
    (W_inv : Matrix (Fin n) (Fin n) ℝ) (hinv : gramian A B k * W_inv = 1) (x₁ : Fin n → ℝ) :
    (∑ i : Fin k, (A ^ (k - 1 - (i : ℕ))) *ᵥ (B *ᵥ steerControl A B k W_inv x₁ i)) = x₁ := by
  have h_term : ∀ i : Fin k,
      (A ^ (k - 1 - (i : ℕ))) *ᵥ (B *ᵥ steerControl A B k W_inv x₁ i) =
      ((A ^ (k - 1 - (i : ℕ))) * B * Bᵀ * (A ^ (k - 1 - (i : ℕ)))ᵀ * W_inv) *ᵥ x₁ := by
    intro i
    unfold steerControl
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  simp_rw [h_term, ← sum_mulVec, ← Matrix.sum_mul]
  have h_rev : ∑ i : Fin k, (A ^ (k - 1 - (i : ℕ))) * B * Bᵀ * (A ^ (k - 1 - (i : ℕ)))ᵀ =
      gramian A B k := by
    rw [gramian_eq_sum_fin]
    have hcomp := (Equiv.sum_comp Fin.revPerm
      (fun i : Fin k => term A B (i : ℕ))).symm
    rw [hcomp]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.revPerm_apply]
    have h_idx : k - 1 - (i : ℕ) = (i.rev : ℕ) := by
      rw [Fin.val_rev]
      omega
    unfold term
    rw [h_idx]
  rw [h_rev, hinv, one_mulVec]

end ControlsLean.Controls
