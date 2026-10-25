# Multivariate Kalman Filter: Joseph-Form Covariance Update, Completion of Squares, and MMSE Trace Optimality in Lean 4

**Author**: Mike Helsel  
**Date**: October 18, 2026  
**Status**: Machine-Checked & Verified (`ControlsLean.Estimation.KalmanOptimality`)  
**Target Repository**: `ctrl` (`ControlsLean/Estimation/KalmanOptimality.lean`)  
**Axiom Footprint**: Standard Lean 4 axioms only (`[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero custom axioms)

---

## 1. Abstract

We present a machine-checked formalization in Lean 4 of the multivariate Kalman filter measurement update in $M_n(\mathbb{R})$, establishing the Bucy–Joseph stabilized covariance update, the matrix completion-of-squares identity, Loewner (quadratic form) optimality across all state directions $x \in \mathbb{R}^n$, and minimum mean-square error (MMSE) trace optimality $\mathrm{tr}(P^+(K^*)) \le \mathrm{tr}(P^+(K))$.

In multi-dimensional linear state estimation with prior state error covariance $P \in \mathbb{R}^{n \times n}$, observation matrix $C \in \mathbb{R}^{m \times n}$, and measurement noise covariance $R \in \mathbb{R}^{m \times m}$, a linear observer with gain matrix $K \in \mathbb{R}^{n \times m}$ updates the state estimate via $\hat{x}^+ = \hat{x} + K(z - C\hat{x})$. The resulting posterior estimation error covariance is given by the **Bucy–Joseph stabilized formula**:
$$P^+(K) = (I - K C) P (I - K C)^\top + K R K^\top.$$

We formalize and machine-check six core results in `ControlsLean.Estimation.KalmanOptimality`:
1. **Symmetry & Positive Semidefiniteness Preservation (`josephCov_transpose`, `quad_josephCov_nonneg`)**: If $P^\top = P$ and $R^\top = R$, then $(P^+(K))^\top = P^+(K)$ for every gain $K$. If $P \succeq 0$ and $R \succeq 0$, then $P^+(K) \succeq 0$ for every gain $K$ (guaranteeing numerical and theoretical covariance validity even for suboptimal gains).
2. **Optimal Kalman Gain Reductions (`josephCov_opt_eq_sub`, `josephCov_opt_eq_one_sub_mul`)**: Whenever $K^*$ satisfies the optimal normal equation $K^* S = P C^\top$ with innovation covariance $S = C P C^\top + R$, the Joseph update reduces to both standard textbook forms:
   $$P^+(K^*) = P - K^* S (K^*)^\top = (I - K^* C) P.$$
3. **Matrix Completion of Squares (`josephCov_completion_of_squares`)**: For any arbitrary gain matrix $K \in \mathbb{R}^{n \times m}$,
   $$P^+(K) = P^+(K^*) + (K - K^*) S (K - K^*)^\top.$$
4. **Loewner / Quadratic Form Optimality (`quad_josephCov_le`)**: If $S \succeq 0$, then for every state direction $x \in \mathbb{R}^n$ and any gain $K$,
   $$x^\top P^+(K^*) x \le x^\top P^+(K) x.$$
5. **Exact Trace Decomposition (`trace_josephCov_eq`)**: By expressing the matrix trace as the sum of quadratic forms along the standard basis vectors $e_i = \mathrm{Pi.single}\; i\; 1$,
   $$\mathrm{tr}(P^+(K)) = \mathrm{tr}(P^+(K^*)) + \sum_{i \in n} ((K - K^*)^\top e_i)^\top S ((K - K^*)^\top e_i).$$
6. **MMSE Trace Optimality (`trace_josephCov_le`, `trace_josephCov_le_of_psd`)**: The optimal Kalman gain $K^*$ globally minimizes the posterior error covariance trace $\mathrm{tr}(P^+(K)) = \mathbb{E}[\|x - \hat{x}^+\|_2^2]$ over all gain matrices $K \in \mathbb{R}^{n \times m}$:
   $$\mathrm{tr}(P^+(K^*)) \le \mathrm{tr}(P^+(K)).$$

---

## 2. Mathematical Formulation

### 2.1 The Bucy–Joseph Stabilized Covariance Update
Let $n$ and $m$ be finite index types (`[Fintype n] [DecidableEq n] [Fintype m]`). For prior error covariance $P \in \mathbb{R}^{n \times n}$, measurement matrix $C \in \mathbb{R}^{m \times n}$, sensor noise covariance $R \in \mathbb{R}^{m \times m}$, and arbitrary linear estimator gain $K \in \mathbb{R}^{n \times m}$, the posterior covariance update is:
$$\mathrm{josephCov}(P, C, R, K) = (I - K C) P (I - K C)^\top + K R K^\top.$$
The innovation covariance matrix is:
$$S = \mathrm{innovCov}(P, C, R) = C P C^\top + R \in \mathbb{R}^{m \times m}.$$

Expanding the matrix products (`josephCov_expand`) yields:
$$P^+(K) = P - P C^\top K^\top - K C P + K S K^\top.$$

### 2.2 Normal Equations and Matrix Completion of Squares
Suppose $P^\top = P$ and $R^\top = R$, which implies $S^\top = S$ (`innovCov_transpose`). Let $K^* \in \mathbb{R}^{n \times m}$ satisfy the linear normal equation:
$$K^* S = P C^\top.$$
Note that formulating the optimality condition via the linear equation $K^* S = P C^\top$ rather than $K^* = P C^\top S^{-1}$ avoids artificial matrix inversion hypotheses while holding identically whenever $K^* = P C^\top S^{-1}$ for invertible $S$.

Taking the transpose of $K^* S = P C^\top$ and using symmetry of $P$ and $S$ yields the dual identity (`innovCov_mul_transpose_opt`):
$$S (K^*)^\top = C P.$$
Substituting $P C^\top = K^* S$ and $C P = S (K^*)^\top$ into `josephCov_expand` at $K = K^*$ cancels two of the three quadratic terms (`josephCov_opt_eq_sub`, `josephCov_opt_eq_one_sub_mul`):
$$P^+(K^*) = P - K^* S (K^*)^\top = (I - K^* C) P.$$
For an arbitrary gain $K$, substituting the same identities into `josephCov_expand` gives:
$$\begin{aligned}
P^+(K) &= P - K^* S K^\top - K S (K^*)^\top + K S K^\top \\
&= \bigl(P - K^* S (K^*)^\top\bigr) + \bigl(K S K^\top - K S (K^*)^\top - K^* S K^\top + K^* S (K^*)^\top\bigr) \\
&= P^+(K^*) + (K - K^*) S (K - K^*)^\top.
\end{aligned}$$
This establishes `josephCov_completion_of_squares`.

### 2.3 Loewner Order and MMSE Trace Optimality
For any vector $x \in \mathbb{R}^n$ and matrices $D \in \mathbb{R}^{n \times m}$, $S \in \mathbb{R}^{m \times m}$, the congruence identity (`quad_conj_transpose`) gives:
$$x^\top (D S D^\top) x = (D^\top x)^\top S (D^\top x).$$
Applying this to $D = K - K^*$ yields the exact quadratic form decomposition (`quad_josephCov_eq`):
$$x^\top P^+(K) x = x^\top P^+(K^*) x + ((K - K^*)^\top x)^\top S ((K - K^*)^\top x).$$
Whenever $S$ is positive semidefinite ($\forall y \in \mathbb{R}^m, 0 \le y^\top S y$), the excess quadratic term is non-negative, establishing Loewner optimality (`quad_josephCov_le`):
$$x^\top P^+(K^*) x \le x^\top P^+(K) x \qquad (\forall x \in \mathbb{R}^n).$$

Finally, for any matrix $M \in \mathbb{R}^{n \times n}$, evaluating its quadratic form on the $i$-th standard basis vector $e_i = \mathrm{Pi.single}\; i\; 1$ extracts the $i$-th diagonal entry (`single_one_dotProduct_mulVec`):
$$e_i^\top M e_i = M_{i,i}.$$
Summing over $i \in n$ expresses the trace as the sum of basis quadratic forms (`trace_eq_sum_quad_single`):
$$\mathrm{tr}(M) = \sum_{i \in n} e_i^\top M e_i.$$
Summing `quad_josephCov_le` across all $i \in n$ via `Finset.sum_le_sum` immediately proves global trace (MMSE) optimality (`trace_josephCov_le`):
$$\mathrm{tr}(P^+(K^*)) \le \mathrm{tr}(P^+(K)),$$
completely avoiding Cholesky factorizations or spectral decompositions.

---

## 3. Formalization Architecture in Lean 4

The complete formalization is implemented in `ControlsLean/Estimation/KalmanOptimality.lean`.

### 3.1 Definitions and Headline Theorems
```lean
/-- The Bucy–Joseph stabilized covariance update for an arbitrary estimator gain `K`. -/
def josephCov (P : Matrix n n ℝ) (C : Matrix m n ℝ) (R : Matrix m m ℝ)
    (K : Matrix n m ℝ) : Matrix n n ℝ :=
  (1 - K * C) * P * (1 - K * C)ᵀ + K * R * Kᵀ

/-- The measurement innovation covariance matrix `S = C P Cᵀ + R`. -/
def innovCov (P : Matrix n n ℝ) (C : Matrix m n ℝ) (R : Matrix m m ℝ) :
    Matrix m m ℝ :=
  C * P * Cᵀ + R

/-- **Headline Theorem 1 — Symmetry of the Joseph Covariance Update**: -/
theorem josephCov_transpose {P : Matrix n n ℝ} (C : Matrix m n ℝ) {R : Matrix m m ℝ}
    (K : Matrix n m ℝ) (hP : Pᵀ = P) (hR : Rᵀ = R) :
    (josephCov P C R K)ᵀ = josephCov P C R K

/-- **Headline Theorem 2 — Matrix Completion of Squares for the Joseph Update**: -/
theorem josephCov_completion_of_squares {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ) (K : Matrix n m ℝ) :
    josephCov P C R K =
      josephCov P C R Kstar + (K - Kstar) * innovCov P C R * (K - Kstar)ᵀ

/-- **Headline Theorem 3 — Loewner / Quadratic Form Optimality of the Kalman Gain**: -/
theorem quad_josephCov_le {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ)
    (hS : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (innovCov P C R *ᵥ y))
    (K : Matrix n m ℝ) (x : n → ℝ) :
    x ⬝ᵥ (josephCov P C R Kstar *ᵥ x) ≤ x ⬝ᵥ (josephCov P C R K *ᵥ x)

/-- **Headline Theorem 4 — Trace (MMSE) Optimality of the Multivariate Kalman Gain**: -/
theorem trace_josephCov_le {P : Matrix n n ℝ} {C : Matrix m n ℝ} {R : Matrix m m ℝ}
    {Kstar : Matrix n m ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : Kstar * innovCov P C R = P * Cᵀ)
    (hS : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ (innovCov P C R *ᵥ y))
    (K : Matrix n m ℝ) :
    Matrix.trace (josephCov P C R Kstar) ≤ Matrix.trace (josephCov P C R K)
```

---

## 4. Novelty Analysis & Gap Positioning

### 4.1 Comparison against Seed Codebase (`ScalarKalman` & `InformationFilter`)
- `ControlsLean.Estimation.ScalarKalman` proves completion of squares `postVar P R k = postVarOpt P R + (P + R) * (k - gain P R) ^ 2` and optimality `postVarOpt_le_postVar` only for 1D scalars $P, R, k \in \mathbb{R}$.
- `ControlsLean.Estimation.InformationFilter` proves algebraic inverse duality between $(P^+)^{-1}$ and $P^{-1} + C^\top R^{-1} C$ in an associative ring, but does not formalize the Joseph update, Loewner PSD ordering, or minimum-trace optimality.
- `ControlsLean.Estimation.KalmanOptimality` bridges both modules by lifting the scalar completion-of-squares and variance minimization of `ScalarKalman` to full $n \times n$ state covariance matrices and $m \times n$ rectangular measurement matrices over $\mathbb{R}$.

### 4.2 Comparison against Mathlib and `LeanForControl`
- Neither Mathlib nor `LeanForControl` contains any formalization of the Bucy–Joseph covariance update, the multivariate Kalman completion-of-squares identity, or MMSE trace optimality.

---

## 5. Literature Grounding & Citations

1. **Bucy, R. S., & Joseph, P. D.** (1968). *Filtering for Stochastic Processes with Applications to Guidance*. Interscience Publishers / Wiley, New York.
   - *Significance*: Introduced the stabilized covariance update $P^+ = (I - K C) P (I - K C)^\top + K R K^\top$ to preserve symmetry and positive semidefiniteness under finite-precision arithmetic and suboptimal gains.
2. **Anderson, B. D. O., & Moore, J. B.** (1979). *Optimal Filtering*. Prentice-Hall, Englewood Cliffs, NJ.
   - *Significance*: Chapter 3 derives the optimal Kalman gain via matrix completion of squares and proves minimum error covariance in the Loewner and trace orders.
3. **Kailath, T., Sayed, A. H., & Hassibi, B.** (2000). *Linear Estimation*. Prentice Hall, Upper Saddle River, NJ.
   - *Significance*: Chapter 9 develops the normal equations $K^* S = P C^\top$ and the orthogonal decomposition of the posterior error covariance.

---

## 6. Verification and Machine-Checked Proof Audit

- **Single-File Verification Command**:
  ```bash
  export PATH="$HOME/.elan/bin:$PATH" && lake env lean ControlsLean/Estimation/KalmanOptimality.lean
  ```
- **Axiomatic Footprint**:
  - `josephCov_transpose`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
  - `josephCov_completion_of_squares`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
  - `josephCov_opt_eq_sub`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
  - `josephCov_opt_eq_one_sub_mul`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
  - `quad_josephCov_le`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
  - `trace_josephCov_le`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
  - `trace_josephCov_le_of_psd`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
- **Zero Escape Hatches**: Zero `sorry`, zero `admit`, zero custom `axiom`s.
