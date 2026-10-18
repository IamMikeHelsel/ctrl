/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import ControlsLean.Estimation.ScalarKalman

/-!
# Multivariate Kalman Filter: Joseph-Form Covariance Update and MMSE Trace Optimality

This module formalizes the multivariate Kalman filter measurement update in $\mathbb{R}^{n \times n}$,
its Bucy–Joseph stabilized covariance form, the matrix completion-of-squares identity,
and minimum mean-square error (MMSE) optimality in both the Loewner (quadratic form) order
and the matrix trace order.

## Mathematical Formulation

Given prior error covariance $P \in \mathbb{R}^{n \times n}$, observation matrix
$C \in \mathbb{R}^{m \times n}$, and measurement noise covariance $R \in \mathbb{R}^{m \times m}$:

1. **Joseph Stabilized Covariance Update (`josephCov P C R K`)**:
   For an arbitrary linear estimator gain matrix $K \in \mathbb{R}^{n \times m}$, the posterior
   estimation error covariance is given by the Bucy–Joseph stabilized update:
   $$P^+(K) = (I - K C) P (I - K C)^\top + K R K^\top.$$

2. **Innovation Covariance (`innovCov P C R`)**:
   $$S = C P C^\top + R \in \mathbb{R}^{m \times m}.$$

3. **Symmetry Preservation and PSD Preservation (`josephCov_transpose`, `quad_josephCov_nonneg`)**:
   If $P^\top = P$ and $R^\top = R$, then $(P^+(K))^\top = P^+(K)$ for every gain $K$.
   Moreover, if $P \succeq 0$ and $R \succeq 0$, then $P^+(K) \succeq 0$ for every gain $K$.

4. **Completing the Square Identity (`josephCov_completion_of_squares`)**:
   If $P^\top = P$, $R^\top = R$, and $K^*$ satisfies the optimal Kalman gain equation
   $K^* S = P C^\top$, then for any gain matrix $K \in \mathbb{R}^{n \times m}$:
   $$P^+(K) = P^+(K^*) + (K - K^*) S (K - K^*)^\top,$$
   where the optimal posterior covariance simplifies to
   $$P^+(K^*) = P - K^* S (K^*)^\top = (I - K^* C) P.$$

5. **Loewner / Quadratic Form Optimality (`quad_josephCov_le`)**:
   If the innovation covariance $S$ is positive semidefinite ($\forall y, 0 \le y^\top S y$),
   then for every state direction $x \in \mathbb{R}^n$ and any gain $K$:
   $$x^\top P^+(K^*) x \le x^\top P^+(K) x.$$

6. **Trace (MMSE) Optimality (`trace_josephCov_le`)**:
   Minimizing the quadratic form along every coordinate axis $e_i$ simultaneously minimizes the
   total mean-square estimation error $\mathrm{tr}(P^+(K))$:
   $$\mathrm{tr}(P^+(K^*)) \le \mathrm{tr}(P^+(K)).$$

## References

* Bucy, R. S., & Joseph, P. D. (1968). *Filtering for Stochastic Processes with Applications
  to Guidance*. Interscience Publishers / Wiley, New York.
* Anderson, B. D. O., & Moore, J. B. (1979). *Optimal Filtering*. Prentice-Hall, Chapter 3.
* Kailath, T., Sayed, A. H., & Hassibi, B. (2000). *Linear Estimation*. Prentice Hall,
  Chapter 9.
-/

namespace ControlsLean.Estimation

open Matrix BigOperators

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

/-! ### Core Definitions: Joseph Covariance Update and Innovation Covariance -/

/-- The Bucy–Joseph stabilized covariance update for an arbitrary estimator gain `K`:
$$P^+(K) = (I - K C) P (I - K C)^\top + K R K^\top.$$ -/
def josephCov (P : Matrix n n ℝ) (C : Matrix m n ℝ) (R : Matrix m m ℝ)
    (K : Matrix n m ℝ) : Matrix n n ℝ :=
  (1 - K * C) * P * (1 - K * C)ᵀ + K * R * Kᵀ

/-- The measurement innovation covariance matrix:
$$S = C P C^\top + R.$$ -/
def innovCov (P : Matrix n n ℝ) (C : Matrix m n ℝ) (R : Matrix m m ℝ) :
    Matrix m m ℝ :=
  C * P * Cᵀ + R

/-! ### Symmetry and Expansion Identities -/

omit [DecidableEq n] [Fintype m] in
/-- If `P` and `R` are symmetric, the innovation covariance `S = C P Cᵀ + R` is symmetric. -/
theorem innovCov_transpose {P : Matrix n n ℝ} (C : Matrix m n ℝ) {R : Matrix m m ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) :
    (innovCov P C R)ᵀ = innovCov P C R := by
  unfold innovCov
  simp only [transpose_add, transpose_mul, transpose_transpose, hP, hR, Matrix.mul_assoc]

/-- **Headline Theorem 1 — Symmetry of the Joseph Covariance Update**:
If `Pᵀ = P` and `Rᵀ = R`, then `(josephCov P C R K)ᵀ = josephCov P C R K` for any gain `K`. -/
theorem josephCov_transpose {P : Matrix n n ℝ} (C : Matrix m n ℝ) {R : Matrix m m ℝ}
    (K : Matrix n m ℝ) (hP : Pᵀ = P) (hR : Rᵀ = R) :
    (josephCov P C R K)ᵀ = josephCov P C R K := by
  unfold josephCov
  simp only [transpose_add, transpose_mul, transpose_transpose, hP, hR, Matrix.mul_assoc]

/-- Algebraic expansion of the Joseph covariance update in terms of the innovation covariance `S`:
$$P^+(K) = P - P C^\top K^\top - K C P + K S K^\top.$$ -/
theorem josephCov_expand (P : Matrix n n ℝ) (C : Matrix m n ℝ) (R : Matrix m m ℝ)
    (K : Matrix n m ℝ) :
    josephCov P C R K =
      P - P * Cᵀ * Kᵀ - K * C * P + K * innovCov P C R * Kᵀ := by
  unfold josephCov innovCov
  simp only [transpose_sub, transpose_one, transpose_mul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

/-! ### Optimal Kalman Gain Reductions and Completion of Squares -/

omit [DecidableEq n] in
/-- Transposed normal equation: if `Pᵀ = P`, `Rᵀ = R`, and `Kstar * S = P * Cᵀ`,
then `S * Kstarᵀ = C * P`. -/
theorem innovCov_mul_transpose_opt {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ) :
    innovCov P C R * Kstarᵀ = C * P := by
  calc innovCov P C R * Kstarᵀ
    _ = (Kstar * innovCov P C R)ᵀ := by rw [transpose_mul, innovCov_transpose C hP hR]
    _ = (P * Cᵀ)ᵀ := by rw [hKstar]
    _ = C * P := by rw [transpose_mul, transpose_transpose, hP]

/-- At an optimal Kalman gain `Kstar` satisfying `Kstar * S = P * Cᵀ`, the Joseph covariance
update reduces to `P - Kstar * S * Kstarᵀ`. -/
theorem josephCov_opt_eq_sub {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ) :
    josephCov P C R Kstar = P - Kstar * innovCov P C R * Kstarᵀ := by
  have hSK : innovCov P C R * Kstarᵀ = C * P := innovCov_mul_transpose_opt hP hR hKstar
  rw [josephCov_expand, ← hKstar, Matrix.mul_assoc Kstar C P, ← hSK,
      ← Matrix.mul_assoc Kstar (innovCov P C R) Kstarᵀ]
  abel

/-- At an optimal Kalman gain `Kstar` satisfying `Kstar * S = P * Cᵀ`, the Joseph covariance
update reduces to the standard textbook form `(1 - Kstar * C) * P`. -/
theorem josephCov_opt_eq_one_sub_mul {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ) :
    josephCov P C R Kstar = (1 - Kstar * C) * P := by
  have hSK : innovCov P C R * Kstarᵀ = C * P := innovCov_mul_transpose_opt hP hR hKstar
  rw [josephCov_opt_eq_sub hP hR hKstar, Matrix.mul_assoc Kstar (innovCov P C R) Kstarᵀ,
      hSK, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

/-- **Headline Theorem 2 — Matrix Completion of Squares for the Joseph Update**:
If `Pᵀ = P`, `Rᵀ = R`, and `Kstar` satisfies the optimal Kalman gain equation
`Kstar * innovCov P C R = P * Cᵀ`, then for any gain matrix `K`:
$$P^+(K) = P^+(K^*) + (K - K^*) S (K - K^*)^\top.$$ -/
theorem josephCov_completion_of_squares {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ) (K : Matrix n m ℝ) :
    josephCov P C R K =
      josephCov P C R Kstar + (K - Kstar) * innovCov P C R * (K - Kstar)ᵀ := by
  have hSK : innovCov P C R * Kstarᵀ = C * P := innovCov_mul_transpose_opt hP hR hKstar
  rw [josephCov_expand P C R K, josephCov_opt_eq_sub hP hR hKstar]
  rw [← hKstar, Matrix.mul_assoc K C P, ← hSK]
  simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-! ### Quadratic Form (Loewner Order) Optimality -/

omit [DecidableEq n] in
/-- Congruence identity for quadratic forms:
$$x^\top (D S D^\top) x = (D^\top x)^\top S (D^\top x).$$ -/
theorem quad_conj_transpose (D : Matrix n m ℝ) (S : Matrix m m ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((D * S * Dᵀ) *ᵥ x) = (Dᵀ *ᵥ x) ⬝ᵥ (S *ᵥ (Dᵀ *ᵥ x)) := by
  rw [Matrix.mul_assoc, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
      ← mulVec_mulVec]

omit [DecidableEq n] in
/-- If `P` and `R` are positive semidefinite, the innovation covariance `S = C P Cᵀ + R` is
positive semidefinite. -/
theorem quad_innovCov_nonneg {P : Matrix n n ℝ} (C : Matrix m n ℝ) {R : Matrix m m ℝ}
    (hP_psd : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (P *ᵥ x))
    (hR_psd : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (R *ᵥ y)) (y : m → ℝ) :
    0 ≤ y ⬝ᵥ (innovCov P C R *ᵥ y) := by
  unfold innovCov
  rw [add_mulVec, dotProduct_add, quad_conj_transpose C P y]
  exact add_nonneg (hP_psd (Cᵀ *ᵥ y)) (hR_psd y)

/-- **Joseph Form PSD Preservation**:
If `P` and `R` are positive semidefinite, then `josephCov P C R K` is positive semidefinite
for ANY gain matrix `K` (even suboptimal gains). -/
theorem quad_josephCov_nonneg {P : Matrix n n ℝ} (C : Matrix m n ℝ) {R : Matrix m m ℝ}
    (K : Matrix n m ℝ)
    (hP_psd : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (P *ᵥ x))
    (hR_psd : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (R *ᵥ y)) (x : n → ℝ) :
    0 ≤ x ⬝ᵥ (josephCov P C R K *ᵥ x) := by
  unfold josephCov
  rw [add_mulVec, dotProduct_add,
      quad_conj_transpose (1 - K * C) P x,
      quad_conj_transpose K R x]
  exact add_nonneg (hP_psd ((1 - K * C)ᵀ *ᵥ x)) (hR_psd (Kᵀ *ᵥ x))

/-- Quadratic form decomposition of `josephCov P C R K`:
$$x^\top P^+(K) x = x^\top P^+(K^*) x + ((K - K^*)^\top x)^\top S ((K - K^*)^\top x).$$ -/
theorem quad_josephCov_eq {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ) (K : Matrix n m ℝ) (x : n → ℝ) :
    x ⬝ᵥ (josephCov P C R K *ᵥ x) =
      x ⬝ᵥ (josephCov P C R Kstar *ᵥ x) +
        ((K - Kstar)ᵀ *ᵥ x) ⬝ᵥ (innovCov P C R *ᵥ ((K - Kstar)ᵀ *ᵥ x)) := by
  rw [josephCov_completion_of_squares hP hR hKstar K,
      add_mulVec, dotProduct_add,
      quad_conj_transpose (K - Kstar) (innovCov P C R) x]

/-- **Headline Theorem 3 — Loewner / Quadratic Form Optimality of the Kalman Gain**:
If the innovation covariance `S = innovCov P C R` is positive semidefinite, then for every
state direction `x : n → ℝ` and any gain matrix `K`:
$$x^\top P^+(K^*) x \le x^\top P^+(K) x.$$ -/
theorem quad_josephCov_le {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ)
    (hS : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (innovCov P C R *ᵥ y))
    (K : Matrix n m ℝ) (x : n → ℝ) :
    x ⬝ᵥ (josephCov P C R Kstar *ᵥ x) ≤ x ⬝ᵥ (josephCov P C R K *ᵥ x) := by
  rw [quad_josephCov_eq hP hR hKstar K x]
  linarith [hS ((K - Kstar)ᵀ *ᵥ x)]

/-! ### Trace (Minimum Mean-Square Error) Optimality -/

/-- Evaluating the quadratic form of `M` on the `i`-th standard basis vector `Pi.single i 1`
extracts the `i`-th diagonal entry `M i i`. -/
theorem single_one_dotProduct_mulVec (M : Matrix n n ℝ) (i : n) :
    (Pi.single i (1 : ℝ)) ⬝ᵥ (M *ᵥ (Pi.single i (1 : ℝ))) = M i i := by
  rw [mulVec_single_one, single_dotProduct, one_mul, col_apply]

/-- The trace of any matrix `M` equals the sum of its quadratic forms along the standard basis. -/
theorem trace_eq_sum_quad_single (M : Matrix n n ℝ) :
    Matrix.trace M = ∑ i : n, (Pi.single i (1 : ℝ)) ⬝ᵥ (M *ᵥ (Pi.single i (1 : ℝ))) := by
  simp only [single_one_dotProduct_mulVec, Matrix.trace, Matrix.diag_apply]

/-- Exact trace decomposition of `josephCov P C R K`:
$$\mathrm{tr}(P^+(K)) = \mathrm{tr}(P^+(K^*)) +
  \sum_{i : n} ((K - K^*)^\top e_i)^\top S ((K - K^*)^\top e_i).$$ -/
theorem trace_josephCov_eq {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ) (K : Matrix n m ℝ) :
    Matrix.trace (josephCov P C R K) =
      Matrix.trace (josephCov P C R Kstar) +
        ∑ i : n,
          ((K - Kstar)ᵀ *ᵥ Pi.single i (1 : ℝ)) ⬝ᵥ
            (innovCov P C R *ᵥ ((K - Kstar)ᵀ *ᵥ Pi.single i (1 : ℝ))) := by
  rw [trace_eq_sum_quad_single (josephCov P C R K),
      trace_eq_sum_quad_single (josephCov P C R Kstar),
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact quad_josephCov_eq hP hR hKstar K (Pi.single i (1 : ℝ))

/-- **Headline Theorem 4 — Trace (MMSE) Optimality of the Multivariate Kalman Gain**:
If `Pᵀ = P`, `Rᵀ = R`, `Kstar * innovCov P C R = P * Cᵀ`, and `innovCov P C R` is positive
semidefinite, then `Kstar` minimizes the posterior error covariance trace (total mean-square
estimation error) over all gain matrices `K`:
$$\mathrm{tr}(P^+(K^*)) \le \mathrm{tr}(P^+(K)).$$ -/
theorem trace_josephCov_le {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ)
    (hS : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (innovCov P C R *ᵥ y))
    (K : Matrix n m ℝ) :
    Matrix.trace (josephCov P C R Kstar) ≤ Matrix.trace (josephCov P C R K) := by
  rw [trace_eq_sum_quad_single (josephCov P C R Kstar),
      trace_eq_sum_quad_single (josephCov P C R K)]
  refine Finset.sum_le_sum fun i _ => ?_
  exact quad_josephCov_le hP hR hKstar hS K (Pi.single i (1 : ℝ))

/-- Corollary: Under positive semidefinite prior covariance `P` and noise covariance `R`,
`Kstar` achieves the minimum posterior trace without requiring a separate hypothesis on `S`. -/
theorem trace_josephCov_le_of_psd {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ)
    (hP_psd : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (P *ᵥ x))
    (hR_psd : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (R *ᵥ y))
    (K : Matrix n m ℝ) :
    Matrix.trace (josephCov P C R Kstar) ≤ Matrix.trace (josephCov P C R K) :=
  trace_josephCov_le hP hR hKstar (quad_innovCov_nonneg C hP_psd hR_psd) K

end ControlsLean.Estimation
