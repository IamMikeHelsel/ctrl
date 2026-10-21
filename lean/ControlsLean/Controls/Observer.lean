/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Luenberger State Observers and the Separation Principle

This module formalizes discrete-time Luenberger state observers and the foundational
Separation Principle of linear control theory.

### State Estimation Overview
Consider a discrete-time linear time-invariant (LTI) plant over a commutative ring $R$:
$$x_{k+1} = A x_k + B u_k, \quad y_k = C x_k$$
where $x_k \in R^n$ is the internal system state, $u_k \in R^m$ is the control input, and
$y_k \in R^p$ is the measured output.

When the full state $x_k$ cannot be measured directly, a Luenberger observer reconstructs
an estimate $\hat{x}_k$ by mimicking the nominal plant dynamics while injecting an output
correction term driven by the innovation (measurement residual) $y_k - C \hat{x}_k$:
$$\hat{x}_{k+1} = A \hat{x}_k + B u_k + L (y_k - C \hat{x}_k)$$
where $L \in R^{n \times p}$ is the observer gain matrix.

### Estimation Error Dynamics & Control Invariance
The state estimation error is defined as $e_k = x_k - \hat{x}_k$.
Subtracting the observer update from the plant update gives:
$$e_{k+1} = (A - L C) e_k$$
Crucially, the control input $B u_k$ cancels out completely: the error dynamics is
autonomous and entirely invariant to whatever control inputs are applied. By induction,
$$e_k = (A - L C)^k e_0$$

### The Separation Principle
When closing the loop with observer-based state feedback $u_k = -K \hat{x}_k$, the control
law uses the estimated state instead of the true state. Substituting $\hat{x}_k = x_k - e_k$
yields:
$$u_k = -K x_k + K e_k$$
The augmented state $[x_k; e_k]$ evolves according to the block upper-triangular system:
$$\begin{bmatrix} x_{k+1} \\ e_{k+1} \end{bmatrix} =
  \begin{bmatrix} A - B K & B K \\ 0 & A - L C \end{bmatrix}
  \begin{bmatrix} x_k \\ e_k \end{bmatrix}$$

Because the coupling block is in the upper right and the lower left is identically zero,
the characteristic polynomial and determinant decouple:
$$\det \begin{bmatrix} s I - (A - B K) & -B K \\ 0 & s I - (A - L C) \end{bmatrix} =
  \det(s I - (A - B K)) \cdot \det(s I - (A - L C))$$

This proves the **Separation Principle**:
1. The closed-loop poles consist of the union of the controller poles (roots of
   $\det(s I - (A - B K))$) and the observer poles (roots of $\det(s I - (A - L C))$).
2. The feedback gain $K$ and observer gain $L$ can be designed independently without
   affecting each other's stability eigenvalues.

### Main Theorems
- `observer_error_step`: $e_{k+1} = (A - L C) e_k$.
- `observer_error_step_control_invariant`: Error step is completely invariant to control inputs.
- `observer_error_pow`: $e_k = (A - L C)^k e_0$.
- `observer_deadbeat_error_zero`: If $(A - L C)^d = 0$, the error vanishes at step $d$.
- `observer_deadbeat_error_zero_ge`: For all $k \ge d$, the error remains identically zero.
- `closed_loop_separation_block`: Augmented $[x; e]$ step under observer feedback.
- `closed_loop_separation_det`: Block determinant factorizes into controller and observer parts.
- `closed_loop_separation_charpoly`: Characteristic polynomial factorizes identically for any $s$.

### References
- Luenberger, D. G. (1964). *Observing the state of a linear system*. IEEE Trans. Mil. Electron.
- Luenberger, D. G. (1971). *An introduction to observers*. IEEE Trans. Autom. Control
  16(6):596–602.
- Åström, K. J., & Murray, R. M. (2021). *Feedback Systems: An Introduction for Scientists
  and Engineers* (2nd ed.). Princeton University Press, Chapter 8.
-/

open Matrix

namespace ControlsLean.Controls

variable {n m p : Type*}
variable {R : Type*} [CommRing R]

/-! ### Discrete-Time Plant and Luenberger Observer Definitions -/

/-- Single step of the discrete-time LTI plant: `x_{k+1} = A x_k + B u_k`. -/
def plantStep [Fintype n] [Fintype m]
    (A : Matrix n n R) (B : Matrix n m R) (x : n → R) (u : m → R) : n → R :=
  A *ᵥ x + B *ᵥ u

/-- Measurement output equation of the LTI plant: `y_k = C x_k`. -/
def plantOutput [Fintype n]
    (C : Matrix p n R) (x : n → R) : p → R :=
  C *ᵥ x

/-- Single step of the Luenberger state observer:
`x̂_{k+1} = A x̂_k + B u_k + L (y_k - C x̂_k)`. -/
def observerStep [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (x_hat : n → R) (u : m → R) (y : p → R) : n → R :=
  A *ᵥ x_hat + B *ᵥ u + L *ᵥ (y - C *ᵥ x_hat)

/-- Estimation error vector: `e_k = x_k - x̂_k`. -/
def estimationError (x x_hat : n → R) : n → R :=
  x - x_hat

/-- Plant state trajectory from initial state `x₀` under input sequence `u`. -/
def plantTraj [Fintype n] [Fintype m]
    (A : Matrix n n R) (B : Matrix n m R) (x₀ : n → R) (u : ℕ → (m → R)) : ℕ → (n → R)
  | 0 => x₀
  | k + 1 => plantStep A B (plantTraj A B x₀ u k) (u k)

/-- Observer state trajectory from initial estimate `x_hat₀` given inputs `u`
and plant output measurements. -/
def observerTraj [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (x_hat₀ : n → R) (u : ℕ → (m → R)) (xTraj : ℕ → (n → R)) : ℕ → (n → R)
  | 0 => x_hat₀
  | k + 1 => observerStep A B C L (observerTraj A B C L x_hat₀ u xTraj k)
      (u k) (plantOutput C (xTraj k))

/-- Estimation error trajectory along the coupled plant and observer trajectories. -/
def errorTraj [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (x₀ x_hat₀ : n → R) (u : ℕ → (m → R)) (k : ℕ) : n → R :=
  estimationError (plantTraj A B x₀ u k)
    (observerTraj A B C L x_hat₀ u (plantTraj A B x₀ u) k)

/-! ### Estimation Error Dynamics and Invariance Theorems -/

/-- **Headline Theorem 1: Observer Error Step**:
The error dynamics satisfies `e_{k+1} = (A - L * C) *ᵥ e_k`.
The control input `B *ᵥ u` cancels out completely, rendering the estimation error step
autonomous and invariant to the control signal. -/
theorem observer_error_step [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (x x_hat : n → R) (u : m → R) :
    estimationError (plantStep A B x u)
      (observerStep A B C L x_hat u (plantOutput C x)) =
      (A - L * C) *ᵥ estimationError x x_hat := by
  unfold estimationError plantStep observerStep plantOutput
  simp only [sub_mulVec, mulVec_mulVec, mulVec_sub]
  abel

/-- **Control Invariance of Observer Error**:
Applying any two control inputs `u₁` and `u₂` produces the identical error update. -/
theorem observer_error_step_control_invariant [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (x x_hat : n → R) (u₁ u₂ : m → R) :
    estimationError (plantStep A B x u₁)
      (observerStep A B C L x_hat u₁ (plantOutput C x)) =
    estimationError (plantStep A B x u₂)
      (observerStep A B C L x_hat u₂ (plantOutput C x)) := by
  rw [observer_error_step, observer_error_step]

@[simp] theorem errorTraj_zero [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (x₀ x_hat₀ : n → R) (u : ℕ → (m → R)) :
    errorTraj A B C L x₀ x_hat₀ u 0 = estimationError x₀ x_hat₀ := rfl

theorem errorTraj_succ [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (x₀ x_hat₀ : n → R) (u : ℕ → (m → R)) (k : ℕ) :
    errorTraj A B C L x₀ x_hat₀ u (k + 1) =
      estimationError (plantStep A B (plantTraj A B x₀ u k) (u k))
        (observerStep A B C L (observerTraj A B C L x_hat₀ u (plantTraj A B x₀ u) k) (u k)
          (plantOutput C (plantTraj A B x₀ u k))) := rfl

/-- Single step evolution along the trajectory. -/
theorem observer_error_traj_step [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (x₀ x_hat₀ : n → R) (u : ℕ → (m → R)) (k : ℕ) :
    errorTraj A B C L x₀ x_hat₀ u (k + 1) = (A - L * C) *ᵥ errorTraj A B C L x₀ x_hat₀ u k := by
  rw [errorTraj_succ]
  exact observer_error_step A B C L _ _ (u k)

/-- General power formula for homogeneous linear matrix-vector recursions. -/
theorem linear_dynamics_pow [DecidableEq n] [Fintype n]
    (M : Matrix n n R) (e : ℕ → (n → R))
    (h_step : ∀ k, e (k + 1) = M *ᵥ e k) (k : ℕ) :
    e k = (M ^ k) *ᵥ e 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [h_step, ih, mulVec_mulVec, ← pow_succ']

/-- **Headline Theorem 2: Observer Error Power Formula**:
The estimation error after `k` steps is given explicitly by `e_k = ((A - L * C) ^ k) *ᵥ e₀`. -/
theorem observer_error_pow [DecidableEq n] [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (x₀ x_hat₀ : n → R) (u : ℕ → (m → R)) (k : ℕ) :
    errorTraj A B C L x₀ x_hat₀ u k = ((A - L * C) ^ k) *ᵥ errorTraj A B C L x₀ x_hat₀ u 0 :=
  linear_dynamics_pow (A - L * C) (errorTraj A B C L x₀ x_hat₀ u)
    (observer_error_traj_step A B C L x₀ x_hat₀ u) k

/-- **Zero Initial Error Invariance**:
If the observer is initialized with the true state (`x₀ = x_hat₀`), the estimation
error remains identically zero for all time. -/
theorem observer_error_zero_init [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (x₀ : n → R) (u : ℕ → (m → R)) (k : ℕ) :
    errorTraj A B C L x₀ x₀ u k = 0 := by
  induction k with
  | zero => simp [errorTraj, plantTraj, observerTraj, estimationError]
  | succ k ih => rw [observer_error_traj_step, ih, mulVec_zero]

/-- **Deadbeat Observer Error Extinction**:
If the observer gain `L` makes `A - L * C` nilpotent of degree `d` (i.e. `(A - L * C) ^ d = 0`),
the estimation error vanishes in exactly `d` steps. -/
theorem observer_deadbeat_error_zero [DecidableEq n] [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (d : ℕ) (h_nil : (A - L * C) ^ d = 0) (x₀ x_hat₀ : n → R) (u : ℕ → (m → R)) :
    errorTraj A B C L x₀ x_hat₀ u d = 0 := by
  rw [observer_error_pow, h_nil, zero_mulVec]

/-- **Deadbeat Observer Trajectory for all $k \ge d$**:
Once extinguished at step `d`, the estimation error remains identically zero for all
subsequent steps. -/
theorem observer_deadbeat_error_zero_ge [DecidableEq n] [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (C : Matrix p n R) (L : Matrix n p R)
    (d : ℕ) (h_nil : (A - L * C) ^ d = 0) (x₀ x_hat₀ : n → R) (u : ℕ → (m → R))
    (k : ℕ) (hk : d ≤ k) :
    errorTraj A B C L x₀ x_hat₀ u k = 0 := by
  obtain ⟨c, rfl⟩ := Nat.le.dest hk
  rw [observer_error_pow, pow_add, h_nil, zero_mul, zero_mulVec]

/-! ### Closed-Loop Dynamics and the Separation Principle -/

/-- Augmented closed-loop state matrix representing the combined controller-observer system:
`[A - B * K, B * K; 0, A - L * C]`. -/
def closedLoopMatrix [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (K : Matrix m n R)
    (C : Matrix p n R) (L : Matrix n p R) : Matrix (Sum n n) (Sum n n) R :=
  fromBlocks (A - B * K) (B * K) 0 (A - L * C)

/-- **Headline Theorem 3: Closed-Loop Separation Block Evolution**:
Under observer-based state feedback `u_k = - (K *ᵥ x̂_k)`, the augmented state `[x; e]`
evolves according to the block upper-triangular matrix
`fromBlocks (A - B * K) (B * K) 0 (A - L * C)`. -/
theorem closed_loop_separation_block [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (K : Matrix m n R)
    (C : Matrix p n R) (L : Matrix n p R) (x x_hat : n → R) :
    Sum.elim (plantStep A B x (- (K *ᵥ x_hat)))
      (estimationError (plantStep A B x (- (K *ᵥ x_hat)))
        (observerStep A B C L x_hat (- (K *ᵥ x_hat)) (plantOutput C x))) =
      fromBlocks (A - B * K) (B * K) 0 (A - L * C) *ᵥ
        Sum.elim x (estimationError x x_hat) := by
  rw [observer_error_step]
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add]
  congr 1
  unfold plantStep estimationError
  simp only [sub_mulVec, mulVec_sub, mulVec_neg, mulVec_mulVec]
  abel

/-- Variant of `closed_loop_separation_block` with control input written as `(-K) *ᵥ x̂`. -/
theorem closed_loop_separation_block' [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (K : Matrix m n R)
    (C : Matrix p n R) (L : Matrix n p R) (x x_hat : n → R) :
    Sum.elim (plantStep A B x ((-K) *ᵥ x_hat))
      (estimationError (plantStep A B x ((-K) *ᵥ x_hat))
        (observerStep A B C L x_hat ((-K) *ᵥ x_hat) (plantOutput C x))) =
      fromBlocks (A - B * K) (B * K) 0 (A - L * C) *ᵥ
        Sum.elim x (estimationError x x_hat) := by
  have h : (-K) *ᵥ x_hat = - (K *ᵥ x_hat) := neg_mulVec x_hat K
  rw [h]
  exact closed_loop_separation_block A B K C L x x_hat

/-- Closed-loop block evolution stated via `closedLoopMatrix`. -/
theorem closed_loop_separation_matrix [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (K : Matrix m n R)
    (C : Matrix p n R) (L : Matrix n p R) (x x_hat : n → R) :
    Sum.elim (plantStep A B x (- (K *ᵥ x_hat)))
      (estimationError (plantStep A B x (- (K *ᵥ x_hat)))
        (observerStep A B C L x_hat (- (K *ᵥ x_hat)) (plantOutput C x))) =
      closedLoopMatrix A B K C L *ᵥ Sum.elim x (estimationError x x_hat) :=
  closed_loop_separation_block A B K C L x x_hat

/-- **Headline Theorem 4: Closed-Loop Separation Determinant**:
The determinant of the augmented closed-loop system decouples into the product of the
state-feedback controller determinant and the observer error determinant:
`det (fromBlocks (A - B * K) (B * K) 0 (A - L * C)) = det (A - B * K) * det (A - L * C)`. -/
theorem closed_loop_separation_det [DecidableEq n] [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (K : Matrix m n R)
    (C : Matrix p n R) (L : Matrix n p R) :
    det (fromBlocks (A - B * K) (B * K) 0 (A - L * C)) =
      det (A - B * K) * det (A - L * C) :=
  det_fromBlocks_zero₂₁ (A - B * K) (B * K) (A - L * C)

/-- Block matrix identity for scalar multiples of identity minus upper block-triangular matrix. -/
theorem smul_one_sub_fromBlocks_zero₂₁ [DecidableEq n]
    (A₁₁ A₁₂ A₂₂ : Matrix n n R) (s : R) :
    s • (1 : Matrix (Sum n n) (Sum n n) R) - fromBlocks A₁₁ A₁₂ 0 A₂₂ =
      fromBlocks (s • 1 - A₁₁) (-A₁₂) 0 (s • 1 - A₂₂) := by
  have h1 : (1 : Matrix (Sum n n) (Sum n n) R) = fromBlocks 1 0 0 1 := fromBlocks_one.symm
  rw [h1, fromBlocks_smul]
  ext (i | i) (j | j) <;> simp

/-- **Characteristic Polynomial Decoupling (Separation Principle)**:
The characteristic polynomial of the full observer-controller closed-loop matrix
decouples into the product of the controller and observer characteristic polynomials:
`det (s I - A_cl) = det (s I - (A - B K)) * det (s I - (A - L C))`.
Consequently, the poles (eigenvalues) of the closed-loop system are precisely the
disjoint union of the observer poles and controller poles. -/
theorem closed_loop_separation_charpoly [DecidableEq n] [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n R) (B : Matrix n m R) (K : Matrix m n R)
    (C : Matrix p n R) (L : Matrix n p R) (s : R) :
    det (s • (1 : Matrix (Sum n n) (Sum n n) R) -
      fromBlocks (A - B * K) (B * K) 0 (A - L * C)) =
      det (s • (1 : Matrix n n R) - (A - B * K)) *
      det (s • (1 : Matrix n n R) - (A - L * C)) := by
  rw [smul_one_sub_fromBlocks_zero₂₁]
  exact det_fromBlocks_zero₂₁ (s • 1 - (A - B * K)) (-(B * K)) (s • 1 - (A - L * C))

end ControlsLean.Controls
