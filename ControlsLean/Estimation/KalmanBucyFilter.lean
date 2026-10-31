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
import ControlsLean.Estimation.KalmanOptimality

/-!
# Continuous-Time Kalman–Bucy Filter Generator and Differential Riccati Identities

This module formalizes the algebraic core of the continuous-time Kalman–Bucy filter and the
matrix Differential Riccati Equation (DRE), dual to the discrete Joseph-form identities in
`Estimation/KalmanOptimality.lean`.

## Mathematical Formulation

For the continuous LTI plant `ẋ = A x + w`, `y = C x + v` with white-noise intensities
`E[w wᵀ] = Q`, `E[v vᵀ] = R`, the linear observer
`ẋ̂ = A x̂ + K (y - C x̂)` has error covariance `P` whose time derivative (when it exists) is
the continuous Joseph / Bucy generator

1. **Filter Generator (`filterGen A C Q R P K`)**:
   $$\mathcal{L}(K) = (A - K C) P + P (A - K C)^\top + Q + K R K^\top.$$

2. **Optimal Continuous Kalman Gain**:
   A gain `K* ∈ ℝ^{n × m}` is optimal for `P` when it satisfies the normal equation
   $$K^* R = P C^\top$$
   (equivalently `K* = P Cᵀ R⁻¹` whenever `R` is invertible).

3. **Differential Riccati RHS at an Optimal Gain (`dreOfGain`)**:
   $$\mathcal{R}(P) = A P + P A^\top - K^* R (K^*)^\top + Q.$$
   When `K* R = P Cᵀ`, this coincides with the classical DRE vector field
   `A P + P Aᵀ - P Cᵀ R⁻¹ C P + Q`.

4. **Completion of Squares (`filterGen_completion_of_squares`)**:
   If `Pᵀ = P`, `Rᵀ = R`, and `K* R = P Cᵀ`, then for every gain `K`:
   $$\mathcal{L}(K) = \mathcal{L}(K^*) + (K - K^*) R (K - K^*)^\top.$$

5. **Loewner / Trace Optimality**:
   Whenever `R ⪰ 0`, the excess `(K - K*) R (K - K*)ᵀ` is positive semidefinite, so `K*`
   minimizes both the quadratic form `xᵀ ℒ(K) x` and the trace `tr(ℒ(K))` among all linear
   gains. These inequalities do not establish uniqueness; if `R = 0`, for example, multiple
   gains may attain the same minimum. In particular, along any differentiable covariance
   trajectory with `Ṗ(t) = ℒ(K(t))`, the Kalman–Bucy gain produces the pointwise-minimal
   instantaneous covariance growth rate.

Existence/uniqueness of DRE solutions, geometric convergence to a CARE fixed point, and
continuous-time observer Lyapunov stability are deferred.

## References

* Kalman, R. E., & Bucy, R. S. (1961). New results in linear filtering and prediction theory.
  *Journal of Basic Engineering*, 83(1), 95–108.
* Bucy, R. S., & Joseph, P. D. (1968). *Filtering for Stochastic Processes with Applications
  to Guidance*. Interscience / Wiley.
* Anderson, B. D. O., & Moore, J. B. (1979). *Optimal Filtering*. Prentice-Hall, Chapter 7.
* Kailath, T., Sayed, A. H., & Hassibi, B. (2000). *Linear Estimation*. Prentice Hall, Ch. 9.
-/

namespace ControlsLean.Estimation

open Matrix BigOperators

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-! ### Core Definitions: Continuous Joseph Generator and DRE RHS -/

/-- The continuous-time Bucy–Joseph filter covariance generator for an arbitrary gain `K`:
$$\mathcal{L}(K) = (A - K C) P + P (A - K C)^\top + Q + K R K^\top.$$ -/
def filterGen (A : Matrix n n ℝ) (C : Matrix m n ℝ) (Q : Matrix n n ℝ) (R : Matrix m m ℝ)
    (P : Matrix n n ℝ) (K : Matrix n m ℝ) : Matrix n n ℝ :=
  (A - K * C) * P + P * (A - K * C)ᵀ + Q + K * R * Kᵀ

/-- The Differential Riccati / CARE vector field evaluated at a candidate optimal gain `K`:
$$\mathcal{R}_K(P) = A P + P A^\top - K R K^\top + Q.$$
When `K R = P Cᵀ`, this is the classical DRE right-hand side. -/
def dreOfGain (A : Matrix n n ℝ) (Q : Matrix n n ℝ) (R : Matrix m m ℝ)
    (P : Matrix n n ℝ) (K : Matrix n m ℝ) : Matrix n n ℝ :=
  A * P + P * Aᵀ - K * R * Kᵀ + Q

/-- `P` is a steady-state CARE solution at gain `K` when the optimal gain equation holds and
the DRE right-hand side vanishes. -/
def IsCARESolution (A : Matrix n n ℝ) (C : Matrix m n ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (P : Matrix n n ℝ) (K : Matrix n m ℝ) : Prop :=
  K * R = P * Cᵀ ∧ dreOfGain A Q R P K = 0

/-! ### Symmetry -/

omit [DecidableEq n] [DecidableEq m] in
/-- If `P`, `Q`, and `R` are symmetric, then `filterGen A C Q R P K` is symmetric for every `K`. -/
theorem filterGen_transpose (A : Matrix n n ℝ) (C : Matrix m n ℝ)
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {P : Matrix n n ℝ}
    (K : Matrix n m ℝ) (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hR : Rᵀ = R) :
    (filterGen A C Q R P K)ᵀ = filterGen A C Q R P K := by
  unfold filterGen
  simp only [transpose_add, transpose_mul, transpose_sub, transpose_transpose, hP, hQ, hR,
    Matrix.mul_assoc]
  abel

omit [DecidableEq n] [DecidableEq m] in
/-- If `P` and `Q` are symmetric and `R` is symmetric, then `dreOfGain` is symmetric. -/
theorem dreOfGain_transpose (A : Matrix n n ℝ) {Q : Matrix n n ℝ} {R : Matrix m m ℝ}
    {P : Matrix n n ℝ} (K : Matrix n m ℝ) (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hR : Rᵀ = R) :
    (dreOfGain A Q R P K)ᵀ = dreOfGain A Q R P K := by
  unfold dreOfGain
  simp only [transpose_add, transpose_sub, transpose_mul, transpose_transpose, hP, hQ, hR,
    Matrix.mul_assoc]
  abel

/-! ### Expansion and Optimal-Gain Reduction -/

omit [DecidableEq n] [DecidableEq m] in
/-- Algebraic expansion of the filter generator:
$$\mathcal{L}(K) = A P + P A^\top + Q - K C P - P C^\top K^\top + K R K^\top.$$ -/
theorem filterGen_expand (A : Matrix n n ℝ) (C : Matrix m n ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (P : Matrix n n ℝ) (K : Matrix n m ℝ) :
    filterGen A C Q R P K =
      A * P + P * Aᵀ + Q - K * C * P - P * Cᵀ * Kᵀ + K * R * Kᵀ := by
  unfold filterGen
  simp only [transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

omit [DecidableEq n] [DecidableEq m] in
/-- Transposed normal equation: if `Pᵀ = P`, `Rᵀ = R`, and `K* R = P Cᵀ`, then `R K*ᵀ = C P`. -/
theorem filter_gain_mul_transpose_opt {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R) (hKstar : Kstar * R = P * Cᵀ) :
    R * Kstarᵀ = C * P := by
  calc R * Kstarᵀ
    _ = (Kstar * R)ᵀ := by rw [transpose_mul, hR]
    _ = (P * Cᵀ)ᵀ := by rw [hKstar]
    _ = C * P := by rw [transpose_mul, transpose_transpose, hP]

omit [DecidableEq n] [DecidableEq m] in
/-- At an optimal continuous Kalman gain `K*` with `K* R = P Cᵀ`, the filter generator
reduces to the Differential Riccati right-hand side `dreOfGain A Q R P Kstar`. -/
theorem filterGen_opt_eq_dre {A : Matrix n n ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix n m ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hKstar : Kstar * R = P * Cᵀ) :
    filterGen A C Q R P Kstar = dreOfGain A Q R P Kstar := by
  have hRK : R * Kstarᵀ = C * P := filter_gain_mul_transpose_opt hP hR hKstar
  rw [filterGen_expand, dreOfGain]
  have h1 : Kstar * C * P = Kstar * R * Kstarᵀ := by
    rw [Matrix.mul_assoc Kstar C P, ← hRK, ← Matrix.mul_assoc]
  have h2 : P * Cᵀ * Kstarᵀ = Kstar * R * Kstarᵀ := by
    rw [← hKstar, Matrix.mul_assoc]
  rw [h1, h2]
  abel

/-! ### Completion of Squares -/

omit [DecidableEq n] [DecidableEq m] in
/-- **Headline Theorem — Matrix Completion of Squares for the Continuous Kalman–Bucy Generator**:
If `Pᵀ = P`, `Rᵀ = R`, and `K*` satisfies the optimal gain equation `K* R = P Cᵀ`, then for
any gain matrix `K`:
$$\mathcal{L}(K) = \mathcal{L}(K^*) + (K - K^*) R (K - K^*)^\top.$$ -/
theorem filterGen_completion_of_squares {A : Matrix n n ℝ} {C : Matrix m n ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix n m ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hKstar : Kstar * R = P * Cᵀ) (K : Matrix n m ℝ) :
    filterGen A C Q R P K =
      filterGen A C Q R P Kstar + (K - Kstar) * R * (K - Kstar)ᵀ := by
  have hRK : R * Kstarᵀ = C * P := filter_gain_mul_transpose_opt hP hR hKstar
  rw [filterGen_expand A C Q R P K, filterGen_opt_eq_dre hP hR hKstar, dreOfGain]
  rw [← hKstar, Matrix.mul_assoc K C P, ← hRK]
  simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

omit [DecidableEq n] [DecidableEq m] in
/-- Corollary: at a CARE solution, the filter generator equals the nonnegative excess
`(K - K*) R (K - K*)ᵀ`. -/
theorem filterGen_of_CARE {A : Matrix n n ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix n m ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hCARE : IsCARESolution A C Q R P Kstar) (K : Matrix n m ℝ) :
    filterGen A C Q R P K = (K - Kstar) * R * (K - Kstar)ᵀ := by
  have hKstar : Kstar * R = P * Cᵀ := hCARE.1
  have hdre : dreOfGain A Q R P Kstar = 0 := hCARE.2
  rw [filterGen_completion_of_squares hP hR hKstar K, filterGen_opt_eq_dre hP hR hKstar, hdre,
    zero_add]

/-! ### Quadratic Form (Loewner) Optimality -/

omit [DecidableEq n] [DecidableEq m] in
/-- If `R ⪰ 0`, the continuous Kalman excess `(K - K*) R (K - K*)ᵀ` is positive semidefinite. -/
theorem quad_filter_excess_nonneg {R : Matrix m m ℝ} (D : Matrix n m ℝ)
    (hR : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (R *ᵥ y)) (x : n → ℝ) :
    0 ≤ x ⬝ᵥ ((D * R * Dᵀ) *ᵥ x) := by
  rw [quad_conj_transpose D R x]
  exact hR (Dᵀ *ᵥ x)

omit [DecidableEq n] [DecidableEq m] in
/-- Quadratic form decomposition of `filterGen`:
$$x^\top \mathcal{L}(K) x = x^\top \mathcal{L}(K^*) x +
  ((K - K^*)^\top x)^\top R ((K - K^*)^\top x).$$ -/
theorem quad_filterGen_eq {A : Matrix n n ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix n m ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hKstar : Kstar * R = P * Cᵀ)
    (K : Matrix n m ℝ) (x : n → ℝ) :
    x ⬝ᵥ (filterGen A C Q R P K *ᵥ x) =
      x ⬝ᵥ (filterGen A C Q R P Kstar *ᵥ x) +
        ((K - Kstar)ᵀ *ᵥ x) ⬝ᵥ (R *ᵥ ((K - Kstar)ᵀ *ᵥ x)) := by
  rw [filterGen_completion_of_squares hP hR hKstar K, add_mulVec, dotProduct_add,
    quad_conj_transpose (K - Kstar) R x]

omit [DecidableEq n] [DecidableEq m] in
/-- **Headline Theorem — Loewner Optimality of the Continuous Kalman–Bucy Gain**:
If `R ⪰ 0`, then for every state direction `x` and any gain `K`:
$$x^\top \mathcal{L}(K^*) x \le x^\top \mathcal{L}(K) x.$$ -/
theorem quad_filterGen_le {A : Matrix n n ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix n m ℝ}
    (hP : Pᵀ = P) (hRsym : Rᵀ = R) (hKstar : Kstar * R = P * Cᵀ)
    (hR : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (R *ᵥ y))
    (K : Matrix n m ℝ) (x : n → ℝ) :
    x ⬝ᵥ (filterGen A C Q R P Kstar *ᵥ x) ≤ x ⬝ᵥ (filterGen A C Q R P K *ᵥ x) := by
  rw [quad_filterGen_eq hP hRsym hKstar K x]
  linarith [hR ((K - Kstar)ᵀ *ᵥ x)]

/-! ### Trace Optimality (Instantaneous MMSE Growth Rate) -/

omit [DecidableEq m] in
/-- Exact trace decomposition of `filterGen`:
$$\mathrm{tr}(\mathcal{L}(K)) = \mathrm{tr}(\mathcal{L}(K^*)) +
  \sum_i ((K - K^*)^\top e_i)^\top R ((K - K^*)^\top e_i).$$ -/
theorem trace_filterGen_eq {A : Matrix n n ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix n m ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hKstar : Kstar * R = P * Cᵀ) (K : Matrix n m ℝ) :
    Matrix.trace (filterGen A C Q R P K) =
      Matrix.trace (filterGen A C Q R P Kstar) +
        ∑ i : n,
          ((K - Kstar)ᵀ *ᵥ Pi.single i (1 : ℝ)) ⬝ᵥ
            (R *ᵥ ((K - Kstar)ᵀ *ᵥ Pi.single i (1 : ℝ))) := by
  rw [trace_eq_sum_quad_single (filterGen A C Q R P K),
    trace_eq_sum_quad_single (filterGen A C Q R P Kstar), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact quad_filterGen_eq hP hR hKstar K (Pi.single i (1 : ℝ))

omit [DecidableEq m] in
/-- **Headline Theorem — Trace Optimality of the Continuous Kalman–Bucy Gain**:
If `R ⪰ 0`, then `K*` minimizes the instantaneous mean-square error growth rate
`tr(ℒ(K))` over all linear gains:
$$\mathrm{tr}(\mathcal{L}(K^*)) \le \mathrm{tr}(\mathcal{L}(K)).$$ -/
theorem trace_filterGen_le {A : Matrix n n ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix n m ℝ}
    (hP : Pᵀ = P) (hRsym : Rᵀ = R) (hKstar : Kstar * R = P * Cᵀ)
    (hR : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (R *ᵥ y)) (K : Matrix n m ℝ) :
    Matrix.trace (filterGen A C Q R P Kstar) ≤ Matrix.trace (filterGen A C Q R P K) := by
  rw [trace_eq_sum_quad_single (filterGen A C Q R P Kstar),
    trace_eq_sum_quad_single (filterGen A C Q R P K)]
  refine Finset.sum_le_sum fun i _ => ?_
  exact quad_filterGen_le hP hRsym hKstar hR K (Pi.single i (1 : ℝ))

omit [DecidableEq m] in
/-- At a CARE solution with `R ⪰ 0`, every gain produces a nonnegative instantaneous
trace growth rate, and the optimal gain produces zero growth. -/
theorem trace_filterGen_CARE_nonneg {A : Matrix n n ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix n m ℝ}
    (hP : Pᵀ = P) (hRsym : Rᵀ = R)
    (hCARE : IsCARESolution A C Q R P Kstar)
    (hR : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (R *ᵥ y)) (K : Matrix n m ℝ) :
    0 ≤ Matrix.trace (filterGen A C Q R P K) := by
  have hzero : Matrix.trace (filterGen A C Q R P Kstar) = 0 := by
    rw [filterGen_opt_eq_dre (A := A) (C := C) (Q := Q) hP hRsym hCARE.1, hCARE.2]
    simp
  linarith [trace_filterGen_le (A := A) (C := C) (Q := Q) hP hRsym hCARE.1 hR K, hzero]

omit [DecidableEq n] [DecidableEq m] in
/-- Closed-loop Lyapunov identity on CARE solutions:
`(A - K* C) P + P (A - K* C)ᵀ + Q + K* R (K*)ᵀ = 0`. -/
theorem care_lyapunov_identity {A : Matrix n n ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    {R : Matrix m m ℝ} {P : Matrix n n ℝ} {Kstar : Matrix n m ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hCARE : IsCARESolution A C Q R P Kstar) :
    filterGen A C Q R P Kstar = 0 := by
  rw [filterGen_opt_eq_dre hP hR hCARE.1, hCARE.2]

end ControlsLean.Estimation
