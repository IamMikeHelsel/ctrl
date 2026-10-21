/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import ControlsLean.Controls.DiscreteLyapunov

/-!
# Discrete Algebraic Riccati Equation (DARE) and LQR Completion of Squares

This module formalizes the algebraic core of discrete-time infinite-horizon Linear Quadratic
Regulation (LQR) and the Discrete Algebraic Riccati Equation (DARE), dual to the Joseph-form
completion-of-squares identity in `Estimation/KalmanOptimality.lean`.

## Mathematical Formulation

For the discrete LTI plant `x_{k+1} = A x_k + B u_k` with stage cost
`ℓ(x, u) = xᵀ Q x + uᵀ R u` and quadratic cost-to-go `V(x) = xᵀ P x`:

1. **Input Gramian (`inputGram P B R`)**:
   $$S = R + B^\top P B.$$

2. **Optimal LQR Gain Equation**:
   A gain `K* ∈ ℝ^{m × n}` is optimal for `P` when it satisfies the normal equation
   $$S K^* = B^\top P A$$
   (equivalently `K* = S⁻¹ Bᵀ P A` whenever `S` is invertible). The certainty-equivalence
   feedback is then `u = -K* x`.

3. **DARE Operator at an Optimal Gain (`dareOfGain`)**:
   $$\mathcal{T}(P) = A^\top P A - (K^*)^\top S K^* + Q.$$
   A matrix `P` solves the DARE when `P = 𝒯(P)` for some `K*` obeying the gain equation.

4. **Bellman Residual (`bellmanResidual`)**:
   The one-step cost-to-go difference under arbitrary feedback `u = -K x` is encoded by
   $$M(K) = Q + K^\top R K + (A - B K)^\top P (A - B K) - P,$$
   so that `xᵀ M(K) x = ℓ(x, -K x) + V((A - B K) x) - V(x)`.

5. **Completion of Squares (`bellman_completion_of_squares`)**:
   If `Pᵀ = P`, `Rᵀ = R`, and `S K* = Bᵀ P A`, then for every gain `K`:
   $$M(K) = \mathcal{T}(P) - P + (K - K^*)^\top S (K - K^*).$$

6. **LQR Optimality and Closed-Loop Lyapunov Identity**:
   When `P` solves the DARE, `M(K*) = 0` and `M(K) ⪰ 0` whenever `S ⪰ 0`, so `K*` uniquely
   minimizes the one-step Bellman residual. Moreover
   $$V((A - B K^*) x) = V(x) - ℓ(x, -K^* x),$$
   and if the stage cost is strictly positive definite then `A - B K*` is asymptotically stable
   by the discrete Lyapunov theorem.

## References

* Anderson, B. D. O., & Moore, J. B. (1971). *Linear Optimal Control*. Prentice-Hall.
* Lancaster, P., & Rodman, L. (1995). *Algebraic Riccati Equations*. Oxford University Press.
* Hespanha, J. P. (2018). *Linear Systems Theory* (2nd ed.). Princeton University Press, Ch. 20.
-/

namespace ControlsLean.Controls

open Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-! ### Core Definitions -/

/-- The discrete LQR input Gramian / control weighting matrix:
$$S = R + B^\top P B.$$ -/
def inputGram (P : Matrix n n ℝ) (B : Matrix n m ℝ) (R : Matrix m m ℝ) :
    Matrix m m ℝ :=
  R + Bᵀ * P * B

/-- The DARE / discrete Riccati operator evaluated at a candidate optimal gain `K`:
$$\mathcal{T}_K(P) = A^\top P A - K^\top S K + Q, \qquad S = R + B^\top P B.$$
When `S K = Bᵀ P A`, this coincides with the classical DARE map
`Aᵀ P A - Aᵀ P B S⁻¹ Bᵀ P A + Q`. -/
def dareOfGain (A : Matrix n n ℝ) (B : Matrix n m ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (P : Matrix n n ℝ) (K : Matrix m n ℝ) : Matrix n n ℝ :=
  Aᵀ * P * A - Kᵀ * inputGram P B R * K + Q

/-- Closed-loop dynamics matrix under state feedback `u = -K x`: `A_cl = A - B K`. -/
def lqrClosedLoop (A : Matrix n n ℝ) (B : Matrix n m ℝ) (K : Matrix m n ℝ) :
    Matrix n n ℝ :=
  A - B * K

/-- One-step Bellman residual matrix under feedback `u = -K x`:
$$M(K) = Q + K^\top R K + (A - B K)^\top P (A - B K) - P.$$ -/
def bellmanResidual (A : Matrix n n ℝ) (B : Matrix n m ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (P : Matrix n n ℝ) (K : Matrix m n ℝ) : Matrix n n ℝ :=
  Q + Kᵀ * R * K + (lqrClosedLoop A B K)ᵀ * P * lqrClosedLoop A B K - P

/-- `P` solves the DARE at gain `K` when the optimal gain equation and fixed-point identity hold. -/
def IsDareSolution (A : Matrix n n ℝ) (B : Matrix n m ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (P : Matrix n n ℝ) (K : Matrix m n ℝ) : Prop :=
  inputGram P B R * K = Bᵀ * P * A ∧ P = dareOfGain A B Q R P K

/-! ### Symmetry of the Input Gramian -/

omit [DecidableEq n] [DecidableEq m] [Fintype m] in
/-- If `P` and `R` are symmetric, the input Gramian `S = R + Bᵀ P B` is symmetric. -/
theorem inputGram_transpose {P : Matrix n n ℝ} (B : Matrix n m ℝ) {R : Matrix m m ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) :
    (inputGram P B R)ᵀ = inputGram P B R := by
  unfold inputGram
  simp only [transpose_add, transpose_mul, transpose_transpose, hP, hR, Matrix.mul_assoc]

omit [DecidableEq n] [DecidableEq m] in
/-- Congruence identity: `xᵀ (Dᵀ S D) x = (D x)ᵀ S (D x)`. -/
theorem quad_conj (D : Matrix m n ℝ) (S : Matrix m m ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((Dᵀ * S * D) *ᵥ x) = (D *ᵥ x) ⬝ᵥ (S *ᵥ (D *ᵥ x)) := by
  rw [Matrix.mul_assoc, ← mulVec_mulVec, dotProduct_mulVec _ Dᵀ, vecMul_transpose,
    ← mulVec_mulVec]

omit [DecidableEq n] [DecidableEq m] in
theorem quad_conj' (D : Matrix m n ℝ) (S : Matrix m m ℝ) (x : n → ℝ) :
    quad (Dᵀ * S * D) x = quad S (D *ᵥ x) :=
  quad_conj D S x

omit [DecidableEq n] [DecidableEq m] in
theorem quad_add' (M N : Matrix n n ℝ) (x : n → ℝ) :
    quad (M + N) x = quad M x + quad N x := by
  simp [quad, add_mulVec, dotProduct_add]

omit [DecidableEq n] [DecidableEq m] in
/-- If `P ⪰ 0` and `R ⪰ 0`, then `inputGram P B R ⪰ 0`. -/
theorem quad_inputGram_nonneg {P : Matrix n n ℝ} (B : Matrix n m ℝ) {R : Matrix m m ℝ}
    (hP : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (P *ᵥ x))
    (hR : ∀ u : m → ℝ, 0 ≤ u ⬝ᵥ (R *ᵥ u)) (u : m → ℝ) :
    0 ≤ u ⬝ᵥ (inputGram P B R *ᵥ u) := by
  unfold inputGram
  rw [add_mulVec, dotProduct_add]
  have hB : u ⬝ᵥ ((Bᵀ * P * B) *ᵥ u) = (B *ᵥ u) ⬝ᵥ (P *ᵥ (B *ᵥ u)) := by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
      transpose_transpose, ← mulVec_mulVec]
  rw [hB]
  exact add_nonneg (hR u) (hP (B *ᵥ u))

/-! ### Optimal Gain Transpose Identity -/

omit [DecidableEq n] [DecidableEq m] in
/-- Transposed normal equation: if `Pᵀ = P`, `Rᵀ = R`, and `S K* = Bᵀ P A`, then
`K*ᵀ S = Aᵀ P B`. -/
theorem inputGram_mul_transpose_opt {A : Matrix n n ℝ} {P : Matrix n n ℝ} {B : Matrix n m ℝ}
    {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : inputGram P B R * Kstar = Bᵀ * P * A) :
    Kstarᵀ * inputGram P B R = Aᵀ * P * B := by
  calc Kstarᵀ * inputGram P B R
    _ = (inputGram P B R * Kstar)ᵀ := by
        rw [transpose_mul, inputGram_transpose B hP hR]
    _ = (Bᵀ * P * A)ᵀ := by rw [hKstar]
    _ = Aᵀ * P * B := by
        simp only [transpose_mul, transpose_transpose, hP, Matrix.mul_assoc]

omit [DecidableEq n] [DecidableEq m] in
/-- Reassociate `Kᵀ Bᵀ P A` so the optimal gain equation applies on the right. -/
private theorem mul_BPA_reassoc (K : Matrix m n ℝ) (B : Matrix n m ℝ) (P A : Matrix n n ℝ) :
    Kᵀ * Bᵀ * P * A = Kᵀ * (Bᵀ * P * A) := by
  simp [Matrix.mul_assoc]

omit [DecidableEq n] [DecidableEq m] in
/-- Reassociate `Aᵀ P B K` so the transposed gain equation applies on the left. -/
private theorem mul_APB_reassoc (A P : Matrix n n ℝ) (B : Matrix n m ℝ) (K : Matrix m n ℝ) :
    Aᵀ * P * B * K = (Aᵀ * P * B) * K := by
  simp [Matrix.mul_assoc]

/-! ### Expansion of the Bellman Residual -/

omit [DecidableEq n] [DecidableEq m] in
/-- Algebraic expansion of the Bellman residual in terms of the input Gramian:
$$M(K) = Q + A^\top P A - P + K^\top S K - A^\top P B K - K^\top B^\top P A.$$ -/
theorem bellmanResidual_expand (A : Matrix n n ℝ) (B : Matrix n m ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (P : Matrix n n ℝ) (K : Matrix m n ℝ) :
    bellmanResidual A B Q R P K =
      Q + Aᵀ * P * A - P + Kᵀ * inputGram P B R * K
        - Aᵀ * P * B * K - Kᵀ * Bᵀ * P * A := by
  unfold bellmanResidual lqrClosedLoop inputGram
  simp only [transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
    Matrix.mul_add, Matrix.add_mul]
  abel

/-! ### Completion of Squares -/

/-- At an optimal LQR gain `K*` with `S K* = Bᵀ P A`, the Bellman residual reduces to
`dareOfGain A B Q R P Kstar - P`. -/
theorem bellmanResidual_opt_eq {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : inputGram P B R * Kstar = Bᵀ * P * A) :
    bellmanResidual A B Q R P Kstar = dareOfGain A B Q R P Kstar - P := by
  have hSK : Kstarᵀ * inputGram P B R = Aᵀ * P * B :=
    inputGram_mul_transpose_opt hP hR hKstar
  rw [bellmanResidual_expand, dareOfGain]
  have h1 : Aᵀ * P * B * Kstar = Kstarᵀ * inputGram P B R * Kstar := by
    rw [mul_APB_reassoc, ← hSK, Matrix.mul_assoc]
  have h2 : Kstarᵀ * Bᵀ * P * A = Kstarᵀ * inputGram P B R * Kstar := by
    rw [mul_BPA_reassoc, ← hKstar, Matrix.mul_assoc]
  rw [h1, h2]
  abel

/-- **Headline Theorem — Matrix Completion of Squares for Discrete LQR / DARE**:
If `Pᵀ = P`, `Rᵀ = R`, and `K*` satisfies the optimal gain equation
`inputGram P B R * K* = Bᵀ P A`, then for any feedback gain `K`:
$$M(K) = \mathcal{T}(P) - P + (K - K^*)^\top S (K - K^*).$$ -/
theorem bellman_completion_of_squares {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : inputGram P B R * Kstar = Bᵀ * P * A) (K : Matrix m n ℝ) :
    bellmanResidual A B Q R P K =
      dareOfGain A B Q R P Kstar - P
        + (K - Kstar)ᵀ * inputGram P B R * (K - Kstar) := by
  have hSK : Kstarᵀ * inputGram P B R = Aᵀ * P * B :=
    inputGram_mul_transpose_opt hP hR hKstar
  rw [bellmanResidual_expand A B Q R P K, dareOfGain]
  have h1 : Aᵀ * P * B * K = Kstarᵀ * inputGram P B R * K := by
    rw [mul_APB_reassoc, ← hSK, Matrix.mul_assoc]
  have h2 : Kᵀ * Bᵀ * P * A = Kᵀ * inputGram P B R * Kstar := by
    rw [mul_BPA_reassoc, ← hKstar, Matrix.mul_assoc]
  rw [h1, h2]
  simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- On a DARE solution, the optimal Bellman residual vanishes. -/
theorem bellmanResidual_eq_zero_of_dare {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hSol : IsDareSolution A B Q R P Kstar) :
    bellmanResidual A B Q R P Kstar = 0 := by
  rcases hSol with ⟨hKstar, hPeq⟩
  rw [bellmanResidual_opt_eq hP hR hKstar, ← hPeq, sub_self]

/-- On a DARE solution, the completion-of-squares identity simplifies to
`M(K) = (K - K*)ᵀ S (K - K*)`. -/
theorem bellmanResidual_eq_of_dare {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hSol : IsDareSolution A B Q R P Kstar) (K : Matrix m n ℝ) :
    bellmanResidual A B Q R P K =
      (K - Kstar)ᵀ * inputGram P B R * (K - Kstar) := by
  rcases hSol with ⟨hKstar, hPeq⟩
  rw [bellman_completion_of_squares hP hR hKstar K, ← hPeq, sub_self, zero_add]

/-! ### Quadratic-Form Optimality -/

/-- Quadratic form of the completion-of-squares identity. -/
theorem quad_bellman_eq {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : inputGram P B R * Kstar = Bᵀ * P * A) (K : Matrix m n ℝ) (x : n → ℝ) :
    quad (bellmanResidual A B Q R P K) x =
      quad (dareOfGain A B Q R P Kstar - P) x
        + quad (inputGram P B R) ((K - Kstar) *ᵥ x) := by
  rw [bellman_completion_of_squares hP hR hKstar K, quad_add', quad_conj']

/-- **Headline Theorem — Loewner / Quadratic Optimality of the LQR Gain**:
If `S = inputGram P B R` is positive semidefinite, then for every state `x` and any gain `K`:
$$x^\top M(K^*) x \le x^\top M(K) x.$$ -/
theorem quad_bellman_le {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : inputGram P B R * Kstar = Bᵀ * P * A)
    (hS : ∀ u : m → ℝ, 0 ≤ u ⬝ᵥ (inputGram P B R *ᵥ u))
    (K : Matrix m n ℝ) (x : n → ℝ) :
    quad (bellmanResidual A B Q R P Kstar) x ≤ quad (bellmanResidual A B Q R P K) x := by
  have hx := quad_bellman_eq (Q := Q) hP hR hKstar K x
  have hopt : quad (bellmanResidual A B Q R P Kstar) x =
      quad (dareOfGain A B Q R P Kstar - P) x := by
    rw [bellmanResidual_opt_eq hP hR hKstar]
  have hS' : 0 ≤ quad (inputGram P B R) ((K - Kstar) *ᵥ x) := by
    simpa [quad] using hS ((K - Kstar) *ᵥ x)
  linarith [hopt, hx, hS']

/-- On a DARE solution with `S ⪰ 0`, every competing gain has nonnegative Bellman residual. -/
theorem quad_bellman_nonneg_of_dare {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hSol : IsDareSolution A B Q R P Kstar)
    (hS : ∀ u : m → ℝ, 0 ≤ u ⬝ᵥ (inputGram P B R *ᵥ u))
    (K : Matrix m n ℝ) (x : n → ℝ) :
    0 ≤ quad (bellmanResidual A B Q R P K) x := by
  rw [bellmanResidual_eq_of_dare hP hR hSol K, quad_conj']
  simpa [quad] using hS ((K - Kstar) *ᵥ x)

/-! ### Closed-Loop Lyapunov Identity and Asymptotic Stability -/

/-- **Headline Theorem — Closed-Loop Cost Decrease on a DARE Solution**:
If `P` solves the DARE at `K*`, then for every state `x`:
$$V((A - B K^*) x) = V(x) - ℓ(x, -K^* x),$$
i.e. `quad P ((A - B K*) x) + quad Q x + quad R (K* x) = quad P x`. -/
theorem dare_closed_loop_lyapunov {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hSol : IsDareSolution A B Q R P Kstar) (x : n → ℝ) :
    quad P (lqrClosedLoop A B Kstar *ᵥ x) + quad Q x + quad R (Kstar *ᵥ x) = quad P x := by
  have hM := bellmanResidual_eq_zero_of_dare hP hR hSol
  have hx : quad (bellmanResidual A B Q R P Kstar) x = 0 := by simp [hM, quad]
  have hKR : quad (Kstarᵀ * R * Kstar) x = quad R (Kstar *ᵥ x) := quad_conj' Kstar R x
  have hexpand :
      quad (bellmanResidual A B Q R P Kstar) x =
        quad Q x + quad R (Kstar *ᵥ x) + quad P (lqrClosedLoop A B Kstar *ᵥ x) - quad P x := by
    unfold bellmanResidual
    rw [quad_sub, quad_add', quad_add', hKR, quad_mulVec]
  linarith [hexpand, hx]

/-- Dissipation form of the closed-loop Lyapunov identity:
`quad (P - A_clᵀ P A_cl) x = quad Q x + quad R (K* x)`. -/
theorem dare_closed_loop_dissipation {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hSol : IsDareSolution A B Q R P Kstar) (x : n → ℝ) :
    quad (P - (lqrClosedLoop A B Kstar)ᵀ * P * lqrClosedLoop A B Kstar) x =
      quad Q x + quad R (Kstar *ᵥ x) := by
  have h := dare_closed_loop_lyapunov hP hR hSol x
  rw [quad_sub, ← quad_mulVec P (lqrClosedLoop A B Kstar) x]
  linarith

/-- **Headline Theorem — Asymptotic Stability of the LQR Closed Loop**:
If `P` solves the DARE at `K*`, `xᵀ P x > 0` for `x ≠ 0`, and the stage cost
`xᵀ Q x + (K* x)ᵀ R (K* x)` is strictly positive for `x ≠ 0`, then every closed-loop
trajectory `x_{k+1} = (A - B K*) x_k` converges to the origin. -/
theorem dare_closed_loop_tendsto_zero {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix m n ℝ}
    (hP_sym : Pᵀ = P) (hR : Rᵀ = R) (hSol : IsDareSolution A B Q R P Kstar)
    (hP : ∀ x ≠ 0, 0 < quad P x)
    (hCost : ∀ x ≠ 0, 0 < quad Q x + quad R (Kstar *ᵥ x))
    (x₀ : n → ℝ) :
    Filter.Tendsto (fun k : ℕ => (lqrClosedLoop A B Kstar ^ k) *ᵥ x₀) Filter.atTop (nhds 0) := by
  refine tendsto_pow_mulVec_zero (A := lqrClosedLoop A B Kstar) (P := P) hP ?_ x₀
  intro x hx
  have hdiss := dare_closed_loop_dissipation hP_sym hR hSol x
  simpa [hdiss] using hCost x hx

/-- Specialization: if `Q ≻ 0` (strict quadratic) and `R ⪰ 0`, the stage-cost hypothesis of
`dare_closed_loop_tendsto_zero` holds automatically. -/
theorem dare_closed_loop_tendsto_zero_of_posDef_Q {A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix m n ℝ}
    (hP_sym : Pᵀ = P) (hR : Rᵀ = R) (hSol : IsDareSolution A B Q R P Kstar)
    (hP : ∀ x ≠ 0, 0 < quad P x)
    (hQ : ∀ x ≠ 0, 0 < quad Q x)
    (hR_psd : ∀ u : m → ℝ, 0 ≤ u ⬝ᵥ (R *ᵥ u))
    (x₀ : n → ℝ) :
    Filter.Tendsto (fun k : ℕ => (lqrClosedLoop A B Kstar ^ k) *ᵥ x₀) Filter.atTop (nhds 0) := by
  refine dare_closed_loop_tendsto_zero hP_sym hR hSol hP ?_ x₀
  intro x hx
  have hR0 : 0 ≤ quad R (Kstar *ᵥ x) := by
    simpa [quad] using hR_psd (Kstar *ᵥ x)
  linarith [hQ x hx]

end ControlsLean.Controls

