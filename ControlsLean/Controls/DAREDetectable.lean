/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.LQROptimality
import ControlsLean.Controls.LQG

/-!
# Detectability Theory for the DARE, Zero-Step Escape & LQR Quadratic Robustness

`SchurLyapunov.lean` and `DAREUniqueness.lean` prove existence, uniqueness, and closed-loop Schur
stability of the Discrete Algebraic Riccati Equation (DARE) under a strictly positive definite
state weight $Q \succ 0$. In control engineering, however, LQR penalties frequently weight only a
measured performance output $y_k = C x_k$, giving a positive semidefinite state cost
$$Q = C^\top C \succeq 0$$
that may have a nontrivial kernel.

This module relaxes $Q \succ 0$ to **detectability** of $(A, C)$ (`IsDetectable A C`), proving the
full Kwakernaak–Sivan / Wonham discrete-time LQR and Kalman theorem without spectral theory or
complex eigenvalues, and establishes the **discrete-time LQR return-difference and quadratic
robustness identities**:

1. **Factored DARE Dissipation & Zero-Step Escape (`joseph_dissipation_factored`,
   `joseph_zero_dissipation_escape`)**:
   At any solution $P = \mathcal{R}_K(P)$ of the Joseph DARE with $Q = C^\top C$,
   $$x^\top P x - (A_K x)^\top P (A_K x) = \|C x\|_2^2 + (K x)^\top R (K x).$$
   If $(A_K x)^\top P (A_K x) = x^\top P x$ and $R \succ 0$, then $C x = 0$ and $K x = 0$, so the
   closed-loop step coincides with both the open-loop step $A x$ and the observer step
   $(A - L C) x$.

2. **Schur Stability under Detectability (`joseph_schur_of_detectable`,
   `dare_schur_of_detectable`)**:
   If $(A, C)$ is detectable, $R \succ 0$, and $P \succeq 0$ satisfies $P = \mathcal{R}_K(P)$ for
   $Q = C^\top C$, then $A - B K$ is Schur stable.
   *Proof strategy*: Telescoping the one-step dissipation along $x_{k+1} = (A - B K) x_k$ shows that
   $\sum_{k=0}^\infty (\|C x_k\|_2^2 + (K x_k)^\top R (K x_k)) \le x_0^\top P x_0 < \infty$, hence
   $C x_k \to 0$ and $K x_k \to 0$. Rewriting the trajectory as a forced observer system
   $$x_{k+1} = (A - L C) x_k + (L C x_k - B K x_k)$$
   for a stabilizing observer gain $L$ and applying `tendsto_zero_of_schur_forced` from `LQG.lean`
   yields $x_k \to 0$.

3. **Uniqueness, Existence & Infinite-Horizon Optimality under Detectability
   (`dare_unique_of_detectable`, `lqr_existsUnique_of_stabilizable_detectable`,
   `lqr_infinite_horizon_optimal_of_detectable`)**:
   Under $R \succ 0$, $(A, B)$ stabilizable, and $(A, C)$ detectable, the DARE for $Q = C^\top C$
   admits a **unique** symmetric PSD solution $P$, value iteration from $0$ converges to $P$,
   the optimal feedback $u = -K(P) x$ is Schur stabilizing, and $x_0^\top P x_0$ is the optimal
   infinite-horizon LQR cost. By duality (`kalman_steady_state_of_stabilizable_detectable`), the
   steady-state Kalman filter with factored process noise $W = G G^\top \succeq 0$ has a unique
   stabilizing PSD error covariance $\Sigma$.

4. **LQR Return-Difference & Quadratic Gain-Margin Robustness
   (`dare_bellman_return_difference`, `dare_perturbed_lyapunov_dissipation`,
   `dare_perturbed_dissipation_ge_of_margin`)**:
   For any perturbed state-feedback gain $K^* + \Delta K$, the one-step Bellman / Hamiltonian cost
   exceeds that of the optimal gain $K^*$ by the exact quadratic return-difference penalty
   $(\Delta K x)^\top (R + B^\top P B) (\Delta K x) \ge 0$. Whenever a gain perturbation lies within
   the quadratic disk margin $(\Delta K x)^\top (R + B^\top P B) (\Delta K x) \le
   ((K^* + \Delta K) x)^\top R ((K^* + \Delta K) x)$, the perturbed closed loop still dissipates at
   least $x^\top Q x$ at every step.

## References

- H. Kwakernaak, R. Sivan, *Linear Optimal Control Systems* (1972), §6.4.
- P. Lancaster, L. Rodman, *Algebraic Riccati Equations* (1995), Ch. 13.
- D. P. Bertsekas, *Dynamic Programming and Optimal Control*, Vol. I, §4.1.
-/

namespace ControlsLean.Controls

open Matrix Filter Topology BigOperators ControlsLean.Tactics ControlsLean.Estimation

variable {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]

/-! ### 1. Schur Stability, Stabilizability & Detectability Predicates -/

/-- A square matrix $M$ is Schur stable if every trajectory $M^k x$ converges to $0$ as
$k \to \infty$. -/
def IsSchurStable [DecidableEq n] (M : Matrix n n ℝ) : Prop :=
  ∀ x : n → ℝ, Tendsto (fun k : ℕ => (M ^ k) *ᵥ x) atTop (𝓝 0)

/-- The pair $(A, B)$ is stabilizable if there exists a state-feedback gain $K$ such that the
closed-loop matrix $A - B K$ is Schur stable. -/
def IsStabilizable [DecidableEq n] (A : Matrix n n ℝ) (B : Matrix n m ℝ) : Prop :=
  ∃ K : Matrix m n ℝ, IsSchurStable (lqrClosedLoop A B K)

/-- The pair $(A, C)$ is detectable if there exists an observer gain $L$ such that the
estimation error matrix $A - L C$ is Schur stable. -/
def IsDetectable [DecidableEq n] (A : Matrix n n ℝ) (C : Matrix p n ℝ) : Prop :=
  ∃ L : Matrix n p ℝ, IsSchurStable (A - L * C)

omit [Fintype m] in
/-- **Control–Estimation Duality for Detectability**:
$(A, C)$ is detectable if and only if $(A^\top, C^\top)$ is stabilizable. -/
theorem isDetectable_iff_isStabilizable_dual [DecidableEq n]
    (A : Matrix n n ℝ) (C : Matrix p n ℝ) :
    IsDetectable A C ↔ IsStabilizable Aᵀ Cᵀ := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨Lᵀ, ?_⟩
    rw [IsSchurStable, lqrClosedLoop_dual]
    exact schur_transpose hL
  · rintro ⟨K, hK⟩
    refine ⟨Kᵀ, ?_⟩
    have hK' := schur_transpose hK
    have hdual : (lqrClosedLoop Aᵀ Cᵀ K)ᵀ = A - Kᵀ * C := by
      simp [lqrClosedLoop, transpose_sub, transpose_mul]
    rwa [hdual] at hK'

/-! ### 2. Factored State Weight $Q = C^\top C$ and Definite Quadratic Forms -/

omit [Fintype m] in
/-- Quadratic form of a factored weight $C^\top C$ equals the squared Euclidean dot product
$(C x) \cdot (C x)$. -/
theorem quad_transpose_mul_self (C : Matrix p n ℝ) (x : n → ℝ) :
    quad (Cᵀ * C) x = (C *ᵥ x) ⬝ᵥ (C *ᵥ x) := by
  simp only [quad, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

omit [Fintype n] [Fintype m] in
/-- The Euclidean dot product of a real vector with itself is nonnegative. -/
theorem dotProduct_self_nonneg' (y : p → ℝ) : 0 ≤ y ⬝ᵥ y :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)

omit [Fintype n] [Fintype m] in
/-- The Euclidean dot product $y \cdot y$ vanishes if and only if $y = 0$. -/
theorem dotProduct_self_eq_zero_iff {y : p → ℝ} : y ⬝ᵥ y = 0 ↔ y = 0 := by
  constructor
  · intro h
    unfold dotProduct at h
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (y i))).1 h
    ext i
    exact mul_self_eq_zero.1 (h0 i (Finset.mem_univ i))
  · rintro rfl
    simp

omit [Fintype n] [Fintype m] in
/-- For any nonzero vector $y \ne 0$, the Euclidean dot product $y \cdot y$ is strictly positive. -/
theorem dotProduct_self_pos_of_ne_zero {y : p → ℝ} (hy : y ≠ 0) : 0 < y ⬝ᵥ y :=
  lt_of_le_of_ne (dotProduct_self_nonneg' y) (Ne.symm (mt dotProduct_self_eq_zero_iff.1 hy))

omit [Fintype m] in
/-- For any output matrix $C$, the factored weight $C^\top C$ is symmetric positive semidefinite. -/
theorem symPSD_transpose_mul_self (C : Matrix p n ℝ) : SymPSD (Cᵀ * C) := by
  refine ⟨by simp [transpose_mul], fun x => ?_⟩
  rw [quad_transpose_mul_self]
  exact dotProduct_self_nonneg' (C *ᵥ x)

omit [Fintype n] [Fintype p] in
/-- For a positive definite matrix $R \succ 0$, $\operatorname{quad} R u = 0 \iff u = 0$. -/
theorem quad_eq_zero_iff_of_posDef {R : Matrix m m ℝ} (hR : R.PosDef) {u : m → ℝ} :
    quad R u = 0 ↔ u = 0 := by
  rw [posDef_iff_quad_pos] at hR
  constructor
  · intro h
    by_contra hu
    exact (hR.2 u hu).ne' h
  · rintro rfl
    simp [quad]

/-! ### 3. Fundamental DARE Dissipation Identities & Zero-Step Escape Lemma -/

/-- **Fundamental Joseph Closed-Loop Dissipation Identity** for $Q = C^\top C$:
If $P = \mathcal{R}_K(P)$ with $Q = C^\top C$, then along the closed-loop step
$A_K = A - B K$,
$$x^\top P x - (A_K x)^\top P (A_K x) = (C x) \cdot (C x) + (K x)^\top R (K x).$$ -/
theorem joseph_dissipation_factored {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hfix : lqrJosephUpdate P A B (Cᵀ * C) R K = P) (x : n → ℝ) :
    quad P x - quad P (lqrClosedLoop A B K *ᵥ x) =
      (C *ᵥ x) ⬝ᵥ (C *ᵥ x) + quad R (K *ᵥ x) := by
  have h := quad_lqrJosephUpdate P A B (Cᵀ * C) R K x
  rw [hfix, quad_transpose_mul_self] at h
  linarith

/-- **Fundamental DARE Closed-Loop Dissipation Identity** for $Q = C^\top C$:
If $P$ solves the DARE $\mathcal{T}(P) = P$ for $Q = C^\top C$, then with optimal gain
$K = K(P)$ and $A_{\text{cl}} = A - B K$,
$$x^\top P x - (A_{\text{cl}} x)^\top P (A_{\text{cl}} x) =
  (C x) \cdot (C x) + (K x)^\top R (K x).$$ -/
theorem dare_dissipation_factored [DecidableEq m] {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hfix : riccatiMap A B (Cᵀ * C) R P = P) (x : n → ℝ) :
    quad P x - quad P (lqrClosedLoop A B (riccatiGain A B R P) *ᵥ x) =
      (C *ᵥ x) ⬝ᵥ (C *ᵥ x) + quad R (riccatiGain A B R P *ᵥ x) :=
  joseph_dissipation_factored hfix x

/-- **Open-Loop DARE Hessian Dissipation Identity** for $Q = C^\top C$:
If $R \succ 0$, $P \succeq 0$, and $P$ solves the DARE $\mathcal{T}(P) = P$ for $Q = C^\top C$,
then with $K = K(P)$,
$$(C x) \cdot (C x) + (A x)^\top P (A x) - x^\top P x =
  (K x)^\top (R + B^\top P B) (K x).$$ -/
theorem dare_openLoop_dissipation_factored [DecidableEq m] {P A : Matrix n n ℝ}
    {B : Matrix n m ℝ} {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hP : SymPSD P) (hfix : riccatiMap A B (Cᵀ * C) R P = P) (x : n → ℝ) :
    (C *ᵥ x) ⬝ᵥ (C *ᵥ x) + quad P (A *ᵥ x) - quad P x =
      quad (lqrHessian P B R) (riccatiGain A B R P *ᵥ x) := by
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  have hopt := lqrJosephUpdate_opt_eq (Q := Cᵀ * C) hP.1 hR'.1
    (riccatiGain_normal_eq (A := A) (B := B) hR hP)
  have hfix' : lqrJosephUpdate P A B (Cᵀ * C) R (riccatiGain A B R P) = P := hfix
  rw [hfix'] at hopt
  have hq := congr_arg (fun M => quad M x) hopt
  rw [quad_sub, quad_add, quad_transpose_mul_self, ← quad_mulVec, ← quad_mulVec_rect] at hq
  linarith

/-- **Zero-Step Escape Lemma** (Joseph form):
If $R \succ 0$, $P$ satisfies $P = \mathcal{R}_K(P)$ for $Q = C^\top C$, and a state $x$ has zero
one-step Lyapunov decrease ($(A_K x)^\top P (A_K x) = x^\top P x$), then:
1. $C x = 0$ (the state is invisible at the output),
2. $K x = 0$ (the feedback control is inactive),
3. $A_K x = A x$ (the closed-loop step coincides with the open-loop step),
4. $(A - L C) x = A_K x$ for every observer gain $L$ (the closed-loop step coincides with the
   observer error step). -/
theorem joseph_zero_dissipation_escape {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hR : R.PosDef) (hfix : lqrJosephUpdate P A B (Cᵀ * C) R K = P)
    {x : n → ℝ} (hzero : quad P (lqrClosedLoop A B K *ᵥ x) = quad P x) :
    C *ᵥ x = 0 ∧ K *ᵥ x = 0 ∧ lqrClosedLoop A B K *ᵥ x = A *ᵥ x ∧
      ∀ L : Matrix n p ℝ, (A - L * C) *ᵥ x = lqrClosedLoop A B K *ᵥ x := by
  have hdiss := joseph_dissipation_factored hfix x
  rw [hzero, sub_self] at hdiss
  have hC0 : 0 ≤ (C *ᵥ x) ⬝ᵥ (C *ᵥ x) := dotProduct_self_nonneg' (C *ᵥ x)
  have hR0 : 0 ≤ quad R (K *ᵥ x) := quad_nonneg_of_posDef hR (K *ᵥ x)
  have hCeq : (C *ᵥ x) ⬝ᵥ (C *ᵥ x) = 0 := by linarith
  have hReq : quad R (K *ᵥ x) = 0 := by linarith
  have hCx : C *ᵥ x = 0 := dotProduct_self_eq_zero_iff.1 hCeq
  have hKx : K *ᵥ x = 0 := (quad_eq_zero_iff_of_posDef hR).1 hReq
  have hAK : lqrClosedLoop A B K *ᵥ x = A *ᵥ x := by
    simp [lqrClosedLoop, sub_mulVec, ← mulVec_mulVec, hKx]
  refine ⟨hCx, hKx, hAK, fun L => ?_⟩
  rw [hAK, sub_mulVec, ← mulVec_mulVec, hCx, mulVec_zero, sub_zero]

/-- **Zero-Step Escape Lemma** (DARE form):
If $R \succ 0$, $P$ solves the DARE $\mathcal{T}(P) = P$ for $Q = C^\top C$, and
$(A_{\text{cl}} x)^\top P (A_{\text{cl}} x) = x^\top P x$, then $C x = 0$, $K(P) x = 0$,
$A_{\text{cl}} x = A x$, and $(A - L C) x = A_{\text{cl}} x$ for every observer gain $L$. -/
theorem dare_zero_dissipation_escape [DecidableEq m] {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hfix : riccatiMap A B (Cᵀ * C) R P = P)
    {x : n → ℝ}
    (hzero : quad P (lqrClosedLoop A B (riccatiGain A B R P) *ᵥ x) = quad P x) :
    C *ᵥ x = 0 ∧ riccatiGain A B R P *ᵥ x = 0 ∧
      lqrClosedLoop A B (riccatiGain A B R P) *ᵥ x = A *ᵥ x ∧
      ∀ L : Matrix n p ℝ,
        (A - L * C) *ᵥ x = lqrClosedLoop A B (riccatiGain A B R P) *ᵥ x :=
  joseph_zero_dissipation_escape hR hfix hzero

/-! ### 4. Asymptotic / Schur Stability under Detectability -/

omit [Fintype n] [Fintype m] in
/-- If $M$ has strictly positive quadratic form on nonzero vectors and $\operatorname{quad} M (v_k)
\to 0$, then $v_k \to 0$. -/
theorem tendsto_zero_of_quad_tendsto_zero {M : Matrix p p ℝ}
    (hM : ∀ y ≠ 0, 0 < quad M y) {v : ℕ → p → ℝ}
    (hv : Tendsto (fun k => quad M (v k)) atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 0) := by
  obtain ⟨c, hc, hcM⟩ := exists_quad_lower hM
  have hsq : Tendsto (fun k => ‖v k‖ ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k => quad M (v k) / c) atTop (𝓝 0) := by
      simpa using hv.div_const c
    refine squeeze_zero (fun _ => by positivity) (fun k => ?_) hlim
    rw [le_div_iff₀ hc, mul_comm]
    exact hcM (v k)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

omit [Fintype n] [Fintype m] in
/-- If $(v_k) \cdot (v_k) \to 0$ as $k \to \infty$, then $v_k \to 0$. -/
theorem tendsto_zero_of_dotProduct_self_tendsto_zero {v : ℕ → p → ℝ}
    (hv : Tendsto (fun k => (v k) ⬝ᵥ (v k)) atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => ?_
  have hsq : Tendsto (fun k => (v k i) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => sq_nonneg _) (fun k => ?_) hv
    rw [sq]
    exact Finset.single_le_sum (fun j _ => mul_self_nonneg (v k j)) (Finset.mem_univ i)
  have h0 := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs] at h0
  exact tendsto_zero_iff_norm_tendsto_zero.2 h0

/-- **Summability of Output & Control Energy along Closed-Loop Trajectories**:
If $R \succ 0$, $P \succeq 0$, and $P = \mathcal{R}_K(P)$ for $Q = C^\top C$, then along any
closed-loop trajectory $x_k = (A - B K)^k x_0$, the stage energy sequence
$(C x_k) \cdot (C x_k) + (K x_k)^\top R (K x_k)$ is summable. -/
theorem summable_dissipation_of_joseph [DecidableEq n] {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hR : R.PosDef) (hP : SymPSD P) (hfix : lqrJosephUpdate P A B (Cᵀ * C) R K = P)
    (x₀ : n → ℝ) :
    Summable (fun k : ℕ =>
      (C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) ⬝ᵥ (C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) +
        quad R (K *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀))) := by
  refine summable_of_sum_range_le
    (fun k => add_nonneg (dotProduct_self_nonneg' _) (quad_nonneg_of_posDef hR _))
    (c := quad P x₀) fun N => ?_
  have htel : ∑ k ∈ Finset.range N,
      ((C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) ⬝ᵥ (C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) +
        quad R (K *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀))) =
      quad P x₀ - quad P ((lqrClosedLoop A B K ^ N) *ᵥ x₀) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih,
        ← joseph_dissipation_factored hfix ((lqrClosedLoop A B K ^ N) *ᵥ x₀),
        mulVec_mulVec, ← pow_succ']
      ring
  rw [htel]
  linarith [hP.2 ((lqrClosedLoop A B K ^ N) *ᵥ x₀)]

/-- **Output-to-Zero & Control-to-Zero Convergence**:
Under the hypotheses of `summable_dissipation_of_joseph`, both the output sequence
$C (A - B K)^k x_0$ and the control sequence $K (A - B K)^k x_0$ converge to $0$ as
$k \to \infty$. -/
theorem tendsto_output_and_control_zero_of_joseph [DecidableEq n]
    {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ}
    {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hR : R.PosDef) (hP : SymPSD P) (hfix : lqrJosephUpdate P A B (Cᵀ * C) R K = P)
    (x₀ : n → ℝ) :
    Tendsto (fun k : ℕ => C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) atTop (𝓝 0) ∧
      Tendsto (fun k : ℕ => K *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) atTop (𝓝 0) := by
  have hsum := (summable_dissipation_of_joseph hR hP hfix x₀).tendsto_atTop_zero
  have hC_sq : Tendsto (fun k : ℕ =>
      (C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) ⬝ᵥ
        (C *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀))) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dotProduct_self_nonneg' _)
      (fun k => le_add_of_nonneg_right (quad_nonneg_of_posDef hR _)) hsum
  have hK_sq : Tendsto (fun k : ℕ =>
      quad R (K *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀))) atTop (𝓝 0) :=
    squeeze_zero (fun _ => quad_nonneg_of_posDef hR _)
      (fun k => le_add_of_nonneg_left (dotProduct_self_nonneg' _)) hsum
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  exact ⟨tendsto_zero_of_dotProduct_self_tendsto_zero hC_sq,
    tendsto_zero_of_quad_tendsto_zero hR'.2 hK_sq⟩

/-- **Forced Observer Decomposition of the Closed Loop**:
Every closed-loop step $x_{k+1} = (A - B K) x_k$ can be written as an observer error step
$(A - L C) x_k$ driven by the output-control perturbation $L (C x_k) - B (K x_k)$. -/
theorem closedLoop_eq_observer_add_forcing (A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (C : Matrix p n ℝ) (K : Matrix m n ℝ) (L : Matrix n p ℝ) (x : n → ℝ) :
    lqrClosedLoop A B K *ᵥ x =
      (A - L * C) *ᵥ x + (L *ᵥ (C *ᵥ x) - B *ᵥ (K *ᵥ x)) := by
  simp only [lqrClosedLoop, sub_mulVec, ← mulVec_mulVec]
  abel

/-- **Schur Stability of Any Joseph DARE Solution under Detectability**:
If $(A, C)$ is detectable, $R \succ 0$, and $P \succeq 0$ satisfies the Joseph equation
$P = \mathcal{R}_K(P)$ for $Q = C^\top C$, then $A - B K$ is Schur stable. -/
theorem joseph_schur_of_detectable [DecidableEq n] {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {C : Matrix p n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hR : R.PosDef) (hP : SymPSD P) (hdet : IsDetectable A C)
    (hfix : lqrJosephUpdate P A B (Cᵀ * C) R K = P) :
    IsSchurStable (lqrClosedLoop A B K) := by
  obtain ⟨L, hL⟩ := hdet
  intro x₀
  set x : ℕ → n → ℝ := fun k => (lqrClosedLoop A B K ^ k) *ᵥ x₀
  obtain ⟨hCx, hKx⟩ := tendsto_output_and_control_zero_of_joseph hR hP hfix x₀
  have hLCx : Tendsto (fun k => L *ᵥ (C *ᵥ x k)) atTop (𝓝 0) := by
    have hcont : Continuous fun y : p → ℝ => L *ᵥ y :=
      continuous_const.matrix_mulVec continuous_id
    simpa only [mulVec_zero, Function.comp_def] using (hcont.tendsto 0).comp hCx
  have hBKx : Tendsto (fun k => B *ᵥ (K *ᵥ x k)) atTop (𝓝 0) := by
    have hcont : Continuous fun u : m → ℝ => B *ᵥ u :=
      continuous_const.matrix_mulVec continuous_id
    simpa only [mulVec_zero, Function.comp_def] using (hcont.tendsto 0).comp hKx
  have hd : Tendsto (fun k => L *ᵥ (C *ᵥ x k) - B *ᵥ (K *ᵥ x k)) atTop (𝓝 0) := by
    simpa using hLCx.sub hBKx
  have hstep : ∀ k, x (k + 1) = (A - L * C) *ᵥ x k + (L *ᵥ (C *ᵥ x k) - B *ᵥ (K *ᵥ x k)) := by
    intro k
    change (lqrClosedLoop A B K ^ (k + 1)) *ᵥ x₀ = _
    rw [pow_succ', ← mulVec_mulVec]
    exact closedLoop_eq_observer_add_forcing A B C K L (x k)
  exact tendsto_zero_of_schur_forced hL hstep hd

/-- **Headline Theorem 1 — Schur Stability of the DARE Solution under Detectability**:
If $(A, C)$ is detectable, $R \succ 0$, and $P \succeq 0$ solves the DARE
$\mathcal{T}(P) = P$ for $Q = C^\top C$, then the optimal closed loop
$A_{\text{cl}} = A - B K(P)$ is Schur stable. -/
theorem dare_schur_of_detectable [DecidableEq n] [DecidableEq m]
    {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hP : SymPSD P) (hdet : IsDetectable A C)
    (hfix : riccatiMap A B (Cᵀ * C) R P = P) :
    IsSchurStable (lqrClosedLoop A B (riccatiGain A B R P)) :=
  joseph_schur_of_detectable hR hP hdet hfix

/-! ### 5. Uniqueness, Existence & Optimality under Stabilizability and Detectability -/

/-- **Headline Theorem 2 — Uniqueness of the PSD DARE Solution under Detectability**:
If $(A, C)$ is detectable and $R \succ 0$, the DARE for $Q = C^\top C$ has **at most one**
symmetric positive semidefinite solution. -/
theorem dare_unique_of_detectable [DecidableEq n] [DecidableEq m]
    {P P' A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hdet : IsDetectable A C)
    (hP : SymPSD P) (hP' : SymPSD P')
    (hfix : riccatiMap A B (Cᵀ * C) R P = P)
    (hfix' : riccatiMap A B (Cᵀ * C) R P' = P') :
    P = P' :=
  dare_unique_of_stabilizing hR hP hP' hfix hfix'
    (dare_schur_of_detectable hR hP hdet hfix)
    (dare_schur_of_detectable hR hP' hdet hfix')

/-- **Existence of a PSD DARE Solution from Stabilizability alone** (for any $Q \succeq 0$):
If $R \succ 0$, $Q = Q^\top \succeq 0$, and $(A, B)$ is stabilizable, then Riccati value iteration
from $P_0 = 0$ converges to the minimal symmetric PSD solution $P$ of the DARE. -/
theorem dare_exists_of_stabilizable_psd [DecidableEq n] [DecidableEq m]
    {A Q : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hQ : SymPSD Q) (hstab : IsStabilizable A B) :
    ∃ P : Matrix n n ℝ,
      Tendsto (riccatiIter A B Q R) atTop (𝓝 P) ∧
      riccatiMap A B Q R P = P ∧
      SymPSD P ∧
      (∀ k, LoewnerLE (riccatiIter A B Q R k) P) ∧
      (∀ P' : Matrix n n ℝ, SymPSD P' → riccatiMap A B Q R P' = P' → LoewnerLE P P') := by
  obtain ⟨K₀, hK₀⟩ := hstab
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  have hQk : SymPSD (Q + K₀ᵀ * R * K₀) := by
    refine ⟨?_, fun v => ?_⟩
    · simp only [transpose_add, transpose_mul, transpose_transpose, hQ.1, hR'.1,
        Matrix.mul_assoc]
    · rw [quad_add, ← quad_mulVec_rect]
      exact add_nonneg (hQ.2 v) (quad_nonneg_of_posDef hR _)
  obtain ⟨S, hS⟩ := lyapunovSum_tendsto_of_schur hK₀ hQk
  obtain ⟨hSpsd, hSeq⟩ := certificate_of_converse_lyapunov hR hQ K₀ hS
    (lyapunov_tail_tendsto_zero_of_schur hK₀ hQk.1)
  have hcert : LoewnerLE (lqrJosephUpdate S A B Q R K₀) S := by
    rw [hSeq]
    exact LoewnerLE.refl S
  obtain ⟨P, hT, hfix, hP, hle, -, hmin⟩ := dare_exists_of_certificate hR hQ K₀ hSpsd hcert
  exact ⟨P, hT, hfix, hP, hle, hmin⟩

/-- **Headline Theorem 3 — Fundamental LQR Theorem under Stabilizability & Detectability**:
If $R \succ 0$, $(A, B)$ is stabilizable, and $(A, C)$ is detectable, then for $Q = C^\top C$:
1. There exists a **unique** symmetric PSD solution $P$ of the DARE $\mathcal{T}(P) = P$;
2. $P$ satisfies the textbook DARE
   $P = C^\top C + A^\top P A - A^\top P B (R + B^\top P B)^{-1} B^\top P A$;
3. Riccati value iteration $P_0 = 0$, $P_{k+1} = \mathcal{T}(P_k)$ converges to $P$;
4. The optimal feedback $u = -K(P) x$ makes the closed loop $A - B K(P)$ Schur stable. -/
theorem lqr_existsUnique_of_stabilizable_detectable [DecidableEq n] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hstab : IsStabilizable A B) (hdet : IsDetectable A C) :
    ∃ P : Matrix n n ℝ,
      (SymPSD P ∧ riccatiMap A B (Cᵀ * C) R P = P) ∧
      (∀ P', SymPSD P' ∧ riccatiMap A B (Cᵀ * C) R P' = P' → P' = P) ∧
      P = Cᵀ * C + Aᵀ * P * A - Aᵀ * P * B * (lqrHessian P B R)⁻¹ * (Bᵀ * P * A) ∧
      Tendsto (riccatiIter A B (Cᵀ * C) R) atTop (𝓝 P) ∧
      IsSchurStable (lqrClosedLoop A B (riccatiGain A B R P)) := by
  have hQ : SymPSD (Cᵀ * C) := symPSD_transpose_mul_self C
  obtain ⟨P, hT, hfix, hP, -, -⟩ := dare_exists_of_stabilizable_psd hR hQ hstab
  have hschur := dare_schur_of_detectable hR hP hdet hfix
  refine ⟨P, ⟨hP, hfix⟩, fun P' ⟨hP', hfix'⟩ =>
    dare_unique_of_detectable hR hdet hP' hP hfix' hfix, ?_, hT, hschur⟩
  conv_lhs => rw [← hfix]
  exact riccatiMap_standard_form hR hP

/-- **Infinite-Horizon LQR Optimality under Stabilizability & Detectability**:
Under $R \succ 0$, $(A, B)$ stabilizable, and $(A, C)$ detectable, the unique symmetric PSD DARE
solution $P$ for $Q = C^\top C$ and its optimal gain $K = K(P)$ satisfy for every initial state
$x_0$:
1. the feedback $u_k = -K x_k$ has summable stage costs with total cost $x_0^\top P x_0$;
2. every open-loop input sequence $u$ with summable stage costs has total cost $\ge x_0^\top P x_0$.
-/
theorem lqr_infinite_horizon_optimal_of_detectable [DecidableEq n] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hstab : IsStabilizable A B) (hdet : IsDetectable A C) :
    ∃ P : Matrix n n ℝ, (SymPSD P ∧ riccatiMap A B (Cᵀ * C) R P = P) ∧
      (∀ P', SymPSD P' ∧ riccatiMap A B (Cᵀ * C) R P' = P' → P' = P) ∧
      ∀ x₀ : n → ℝ,
        HasSum (fun k => lqrStage (Cᵀ * C) R
            (lqrTraj A B x₀ (fun j => -(riccatiGain A B R P *ᵥ
              ((lqrClosedLoop A B (riccatiGain A B R P) ^ j) *ᵥ x₀))) k)
            (-(riccatiGain A B R P *ᵥ
              ((lqrClosedLoop A B (riccatiGain A B R P) ^ k) *ᵥ x₀))))
          (quad P x₀) ∧
        ∀ u : ℕ → m → ℝ, Summable (fun k => lqrStage (Cᵀ * C) R (lqrTraj A B x₀ u k) (u k)) →
          quad P x₀ ≤ ∑' k, lqrStage (Cᵀ * C) R (lqrTraj A B x₀ u k) (u k) := by
  obtain ⟨P, ⟨hP, hfix⟩, huniq, -, hT, hschur⟩ :=
    lqr_existsUnique_of_stabilizable_detectable hR hstab hdet
  have hQpsd : SymPSD (Cᵀ * C) := symPSD_transpose_mul_self C
  have hstage0 : ∀ x v, 0 ≤ lqrStage (Cᵀ * C) R x v := fun x v =>
    add_nonneg (hQpsd.2 x) (quad_nonneg_of_posDef hR v)
  refine ⟨P, ⟨hP, hfix⟩, huniq, fun x₀ => ⟨?_, fun u hu => ?_⟩⟩
  · rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => hstage0 _ _)]
    have hcost := lqrCost_feedback_eq (Q := Cᵀ * C) (R := R)
      (hfix : lqrJosephUpdate P A B (Cᵀ * C) R (riccatiGain A B R P) = P) x₀
    have hlim : Tendsto (fun N => quad P x₀ -
        quad P ((lqrClosedLoop A B (riccatiGain A B R P) ^ N) *ᵥ x₀)) atTop
        (𝓝 (quad P x₀ - quad P 0)) :=
      tendsto_const_nhds.sub (((continuous_quad P).tendsto 0).comp (hschur x₀))
    have hzero : quad P x₀ - quad P 0 = quad P x₀ := by simp [quad]
    rw [hzero] at hlim
    refine hlim.congr fun N => ?_
    exact (hcost N).symm
  · have hle : ∀ N, quad (riccatiIter A B (Cᵀ * C) R N) x₀ ≤
        ∑' k, lqrStage (Cᵀ * C) R (lqrTraj A B x₀ u k) (u k) := fun N =>
      (riccatiIter_le_lqrCost hR hQpsd N x₀ u).trans
        (hu.sum_le_tsum (Finset.range N) fun k _ => hstage0 _ _)
    exact le_of_tendsto' (tendsto_quad_of_tendsto hT x₀) hle

/-- **Dual Steady-State Kalman Filter under Factored Process Noise $W = G G^\top \succeq 0$**:
If $V \succ 0$, $(A, C)$ is detectable, and $(A, G)$ is stabilizable, then the filtering ARE
with factored process noise covariance $W = G G^\top$ has a **unique** symmetric PSD solution
$\Sigma$, covariance iteration from $0$ converges to $\Sigma$, and the steady-state predictor
error matrix $A - L(\Sigma) C$ is Schur stable. -/
theorem kalman_steady_state_of_stabilizable_detectable [DecidableEq n] [DecidableEq p]
    {A : Matrix n n ℝ} {G : Matrix n m ℝ} {C : Matrix p n ℝ} {V : Matrix p p ℝ}
    (hV : V.PosDef) (hdet : IsDetectable A C) (hstabG : IsStabilizable A G) :
    ∃ Sig : Matrix n n ℝ,
      (SymPSD Sig ∧ kalmanMap A C (G * Gᵀ) V Sig = Sig) ∧
      (∀ Sig', SymPSD Sig' ∧ kalmanMap A C (G * Gᵀ) V Sig' = Sig' → Sig' = Sig) ∧
      Sig = G * Gᵀ + A * Sig * Aᵀ -
        A * Sig * Cᵀ * (V + C * Sig * Cᵀ)⁻¹ * (C * Sig * Aᵀ) ∧
      Tendsto (kalmanIter A C (G * Gᵀ) V) atTop (𝓝 Sig) ∧
      IsSchurStable (A - kalmanGain A C V Sig * C) := by
  have hstab_dual : IsStabilizable Aᵀ Cᵀ :=
    (isDetectable_iff_isStabilizable_dual A C).1 hdet
  have hdet_dual : IsDetectable Aᵀ Gᵀ := by
    rw [isDetectable_iff_isStabilizable_dual, transpose_transpose, transpose_transpose]
    exact hstabG
  have hGG : (Gᵀ)ᵀ * Gᵀ = G * Gᵀ := by simp [transpose_transpose]
  obtain ⟨Sig, ⟨hSig, hfix⟩, huniq, hstd, hT, hschur⟩ :=
    lqr_existsUnique_of_stabilizable_detectable (A := Aᵀ) (B := Cᵀ) (C := Gᵀ) hV hstab_dual
      hdet_dual
  rw [hGG] at hfix huniq hstd hT
  refine ⟨Sig, ⟨hSig, hfix⟩, huniq, ?_, hT, ?_⟩
  · conv_lhs => rw [← hfix]
    exact kalmanMap_standard_form hV hSig
  · have hschur' := schur_transpose hschur
    have hK : riccatiGain Aᵀ Cᵀ V Sig = (kalmanGain A C V Sig)ᵀ := by simp [kalmanGain]
    rw [hK, lqrClosedLoop_dual, transpose_transpose] at hschur'
    exact hschur'

/-! ### 6. LQR Return-Difference & Quadratic Gain-Margin Robustness Identities -/

omit [Fintype p] in
/-- **Perturbed Gain Joseph Matrix Identity**:
For any gain perturbation $\Delta K$ around a gain $K^*$ satisfying the LQR normal equation
$(R + B^\top P B) K^* = B^\top P A$,
$$\mathcal{R}_{K^* + \Delta K}(P) =
  \mathcal{R}_{K^*}(P) + (\Delta K)^\top (R + B^\top P B) (\Delta K).$$ -/
theorem lqr_perturbed_joseph_eq {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A) (ΔK : Matrix m n ℝ) :
    lqrJosephUpdate P A B Q R (Kstar + ΔK) =
      lqrJosephUpdate P A B Q R Kstar + ΔKᵀ * lqrHessian P B R * ΔK := by
  have h := lqr_joseph_completion_of_squares (Q := Q) hP hR hKstar (Kstar + ΔK)
  rwa [add_sub_cancel_left] at h

omit [Fintype p] in
/-- **Quadratic Form of the Perturbed Joseph Update**:
$$x^\top \mathcal{R}_{K^* + \Delta K}(P) x =
  x^\top \mathcal{R}_{K^*}(P) x + (\Delta K x)^\top (R + B^\top P B) (\Delta K x).$$ -/
theorem quad_lqr_perturbed_joseph {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A) (ΔK : Matrix m n ℝ) (x : n → ℝ) :
    quad (lqrJosephUpdate P A B Q R (Kstar + ΔK)) x =
      quad (lqrJosephUpdate P A B Q R Kstar) x +
        quad (lqrHessian P B R) (ΔK *ᵥ x) := by
  rw [lqr_perturbed_joseph_eq hP hR hKstar ΔK, quad_add, quad_mulVec_rect]

omit [Fintype p] in
/-- **Discrete-Time Bellman Return-Difference Identity**:
If $P = \mathcal{R}_{K^*}(P)$ solves the DARE with optimal gain $K^*$ satisfying
$(R + B^\top P B) K^* = B^\top P A$, then for every state $x$ and control input $u$,
$$\ell(x, u) + (A x + B u)^\top P (A x + B u) - x^\top P x =
  (u + K^* x)^\top (R + B^\top P B) (u + K^* x).$$ -/
theorem dare_bellman_return_difference {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A)
    (hfix : lqrJosephUpdate P A B Q R Kstar = P)
    (x : n → ℝ) (u : m → ℝ) :
    lqrStage Q R x u + quad P (A *ᵥ x + B *ᵥ u) - quad P x =
      quad (lqrHessian P B R) (u + Kstar *ᵥ x) := by
  unfold lqrStage
  have h := lqr_bellman_completion_of_squares (Q := Q) hP hR hKstar x u
  rw [hfix] at h
  linarith

omit [Fintype p] in
/-- **Headline Theorem 4 — Perturbed Closed-Loop Lyapunov Dissipation Identity**:
At a DARE solution $P = \mathcal{R}_{K^*}(P)$, the one-step Lyapunov decrease of $V(x) = x^\top P x$
along the perturbed closed loop $A_{K^* + \Delta K} = A - B (K^* + \Delta K)$ is given by
$$x^\top P x - (A_{K^* + \Delta K} x)^\top P (A_{K^* + \Delta K} x) =
  x^\top Q x + ((K^* + \Delta K) x)^\top R ((K^* + \Delta K) x) -
  (\Delta K x)^\top (R + B^\top P B) (\Delta K x).$$ -/
theorem dare_perturbed_lyapunov_dissipation {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A)
    (hfix : lqrJosephUpdate P A B Q R Kstar = P)
    (ΔK : Matrix m n ℝ) (x : n → ℝ) :
    quad P x - quad P (lqrClosedLoop A B (Kstar + ΔK) *ᵥ x) =
      quad Q x + quad R ((Kstar + ΔK) *ᵥ x) -
        quad (lqrHessian P B R) (ΔK *ᵥ x) := by
  have h1 := quad_lqr_perturbed_joseph (Q := Q) hP hR hKstar ΔK x
  rw [hfix, quad_lqrJosephUpdate] at h1
  linarith

omit [Fintype p] in
/-- **Optimal Gain Dominance over Perturbed Gains**:
The optimal LQR gain $K^*$ dominates any perturbed gain $K^* + \Delta K$ in one-step net
Bellman dissipation (Lyapunov decrease minus stage cost) by the exact nonnegative quadratic
return-difference form $(\Delta K x)^\top (R + B^\top P B) (\Delta K x) \ge 0$. -/
theorem dare_optimal_dominates_perturbed_bellman {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : SymPSD P) (hR : R.PosDef)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A)
    (hfix : lqrJosephUpdate P A B Q R Kstar = P)
    (ΔK : Matrix m n ℝ) (x : n → ℝ) :
    (quad P x - quad P (lqrClosedLoop A B Kstar *ᵥ x) -
        (quad Q x + quad R (Kstar *ᵥ x))) -
      (quad P x - quad P (lqrClosedLoop A B (Kstar + ΔK) *ᵥ x) -
        (quad Q x + quad R ((Kstar + ΔK) *ᵥ x))) =
      quad (lqrHessian P B R) (ΔK *ᵥ x) ∧
    0 ≤ quad (lqrHessian P B R) (ΔK *ᵥ x) := by
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  have hopt := quad_lqrJosephUpdate P A B Q R Kstar x
  rw [hfix] at hopt
  have hpert := dare_perturbed_lyapunov_dissipation hP.1 hR'.1 hKstar hfix ΔK x
  refine ⟨by linarith, quad_nonneg_of_posDef (lqrHessian_posDef hR hP) (ΔK *ᵥ x)⟩

omit [Fintype p] in
/-- **Quadratic Disk-Margin / Gain-Margin Robustness Theorem**:
If a gain perturbation $\Delta K$ satisfies the quadratic disk-margin inequality
$$(\Delta K x)^\top (R + B^\top P B) (\Delta K x) \le
  ((K^* + \Delta K) x)^\top R ((K^* + \Delta K) x),$$
then the perturbed closed loop $A - B (K^* + \Delta K)$ still decreases the Lyapunov function
$V(x) = x^\top P x$ by at least the state cost $x^\top Q x$ at every step:
$$x^\top Q x \le x^\top P x - (A_{K^* + \Delta K} x)^\top P (A_{K^* + \Delta K} x).$$ -/
theorem dare_perturbed_dissipation_ge_of_margin {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {Kstar : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hKstar : lqrHessian P B R * Kstar = Bᵀ * P * A)
    (hfix : lqrJosephUpdate P A B Q R Kstar = P)
    {ΔK : Matrix m n ℝ} {x : n → ℝ}
    (hmargin : quad (lqrHessian P B R) (ΔK *ᵥ x) ≤ quad R ((Kstar + ΔK) *ᵥ x)) :
    quad Q x ≤ quad P x - quad P (lqrClosedLoop A B (Kstar + ΔK) *ᵥ x) := by
  rw [dare_perturbed_lyapunov_dissipation hP hR hKstar hfix ΔK x]
  linarith

end ControlsLean.Controls
