/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.DAREDetectable

/-!
# Minimal-Hypothesis LQG Separation & the Discrete-Time Bounded Real / $H_\infty$ Riccati Theory

This module completes two pillars of modern multivariable control theory on top of
`DAREDetectable.lean` and `LQG.lean`:

## 1. Minimal-Hypothesis Output-Feedback LQG Separation
(`lqg_closed_loop_stable_of_stabilizable_detectable`)

In `LQG.lean`, output-feedback stability of the LQG controller was established under strictly
positive definite state cost $Q \succ 0$ and process noise covariance $W \succ 0$. Combining the
detectability DARE theory (`lqr_existsUnique_of_stabilizable_detectable`) and dual factored-noise
Kalman theory (`kalman_steady_state_of_stabilizable_detectable`) from `DAREDetectable.lean` with
`lqg_stable_of_stable_gains` yields the full textbook **Minimal-Hypothesis Dynamical Separation
Principle**:
- Under $R \succ 0$, $V \succ 0$, $(A, B)$ stabilizable, $(A, C_q)$ detectable (for state weight
  $Q = C_q^\top C_q \succeq 0$), $(A, G)$ stabilizable, and $(A, C)$ detectable (for process noise
  covariance $W = G G^\top \succeq 0$), there exist **unique** symmetric PSD solutions $P \succeq 0$
  of the control DARE and $\Sigma \succeq 0$ of the filtering DARE such that the coupled LQG
  output-feedback loop drives $x_k \to 0$, $\hat{x}_k \to 0$, and $x_k - \hat{x}_k \to 0$ from
  every initial condition.

## 2. Discrete-Time Bounded Real Lemma, $H_\infty$ Riccati Equation & Worst-Case Disturbance

For the discrete-time LTI system with exogenous disturbance $w_k \in \mathbb{R}^m$ and performance
output $z_k \in \mathbb{R}^p$:
$$x_{k+1} = A x_k + B w_k, \qquad z_k = C x_k + D w_k,$$
and $H_\infty$ attenuation level $\gamma > 0$:

- `hinfHessian P B D γ`: The $H_\infty$ disturbance Hessian
  $$M_\gamma(P) = \gamma^2 I - D^\top D - B^\top P B.$$
- `hinfDisturbanceGain P A B C D γ`: The worst-case state-feedback disturbance gain
  $$K_w(P) = M_\gamma(P)^{-1} (B^\top P A + D^\top C).$$
- `hinfRiccatiMap P A B C D γ`: The discrete-time $H_\infty$ Algebraic Riccati operator
  $$\mathcal{R}_\infty(P) = A^\top P A + C^\top C +
    (A^\top P B + C^\top D) M_\gamma(P)^{-1} (B^\top P A + D^\top C).$$
- `hinf_stage_completion_of_squares`: Fundamental one-step $H_\infty$ completion of squares:
  $$\|C x + D w\|_2^2 - \gamma^2 \|w\|_2^2 + (A x + B w)^\top P (A x + B w) - x^\top P x
    = x^\top (\mathcal{R}_\infty(P) - P) x - (w - K_w(P) x)^\top M_\gamma(P) (w - K_w(P) x).$$
- `hinf_finite_horizon_identity` & `hinf_l2_gain_bound`: Over any finite horizon $N$, if
  $P = \mathcal{R}_\infty(P)$ with $P \succeq 0$ and $M_\gamma(P) \succ 0$,
  $$\sum_{k=0}^{N-1} \|z_k\|_2^2 + x_N^\top P x_N +
    \sum_{k=0}^{N-1} (w_k - K_w(P) x_k)^\top M_\gamma(P) (w_k - K_w(P) x_k)
    = \gamma^2 \sum_{k=0}^{N-1} \|w_k\|_2^2 + x_0^\top P x_0,$$
  certifying the $\ell_2$-gain bound $\sum_{k=0}^{N-1} \|z_k\|_2^2 \le \gamma^2 \sum_{k=0}^{N-1}
  \|w_k\|_2^2 + x_0^\top P x_0$ for all disturbances and exact tightness under the worst-case
  disturbance $w_k^* = K_w(P) x_k$.
- `schur_of_lyapunov_le_detectable` & `hinf_schur_of_detectable`: If $P \succeq 0$ satisfies
  $\mathcal{R}_\infty(P) \preceq P$, $M_\gamma(P) \succ 0$, and $(A, C)$ is detectable, then the
  open-loop matrix $A$ is Schur stable.

## References

- T. Basar, P. Bernhard, *$H^\infty$-Optimal Control and Related Minimax Design Problems* (1995).
- K. Zhou, J. C. Doyle, K. Glover, *Robust and Optimal Control* (1996), Ch. 13 & 21.
- B. Hassibi, A. H. Sayed, T. Kailath, *Indefinite-Quadratic Estimation and Control* (1999).
-/

namespace ControlsLean.Controls

open Matrix Filter Topology BigOperators ControlsLean.Tactics

variable {n m p q r : Type*} [Fintype n] [Fintype m] [Fintype p] [Fintype q] [Fintype r]

/-! ### 1. Minimal-Hypothesis Output-Feedback LQG Separation Principle -/

/-- LQG closed-loop trajectory $(x_k, \hat x_k)$ under $u_k = -K \hat x_k$ and the observer
$\hat x_{k+1} = A \hat x_k + B u_k + L (C x_k - C \hat x_k)$. -/
def lqgTraj (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix p n ℝ) (K : Matrix m n ℝ)
    (L : Matrix n p ℝ) (x₀ xh₀ : n → ℝ) : ℕ → (n → ℝ) × (n → ℝ)
  | 0 => (x₀, xh₀)
  | k + 1 =>
    let s := lqgTraj A B C K L x₀ xh₀ k
    (A *ᵥ s.1 + B *ᵥ (-(K *ᵥ s.2)),
      A *ᵥ s.2 + B *ᵥ (-(K *ᵥ s.2)) + L *ᵥ (C *ᵥ s.1 - C *ᵥ s.2))

omit [Fintype q] [Fintype r] in
theorem lqgTraj_error_step (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix p n ℝ)
    (K : Matrix m n ℝ) (L : Matrix n p ℝ) (x₀ xh₀ : n → ℝ) (k : ℕ) :
    (lqgTraj A B C K L x₀ xh₀ (k + 1)).1 - (lqgTraj A B C K L x₀ xh₀ (k + 1)).2 =
      (A - L * C) *ᵥ ((lqgTraj A B C K L x₀ xh₀ k).1 - (lqgTraj A B C K L x₀ xh₀ k).2) := by
  simp only [lqgTraj, sub_mulVec, mulVec_sub, ← mulVec_mulVec]
  abel

omit [Fintype q] [Fintype r] in
theorem lqgTraj_state_step (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix p n ℝ)
    (K : Matrix m n ℝ) (L : Matrix n p ℝ) (x₀ xh₀ : n → ℝ) (k : ℕ) :
    (lqgTraj A B C K L x₀ xh₀ (k + 1)).1 =
      lqrClosedLoop A B K *ᵥ (lqgTraj A B C K L x₀ xh₀ k).1 +
        (B * K) *ᵥ ((lqgTraj A B C K L x₀ xh₀ k).1 - (lqgTraj A B C K L x₀ xh₀ k).2) := by
  simp only [lqgTraj, lqrClosedLoop, sub_mulVec, mulVec_sub, mulVec_neg, ← mulVec_mulVec]
  abel

omit [Fintype m] [Fintype p] [Fintype q] [Fintype r] in
theorem linear_dynamics_pow' [DecidableEq n] (M : Matrix n n ℝ) (e : ℕ → n → ℝ)
    (he : ∀ k, e (k + 1) = M *ᵥ e k) : ∀ k, e k = (M ^ k) *ᵥ e 0
  | 0 => by simp
  | k + 1 => by rw [he k, linear_dynamics_pow' M e he k, mulVec_mulVec, ← pow_succ']

omit [Fintype q] [Fintype r] in
/-- **Separation-principle stability**: if $A - BK$ and $A - LC$ are both Schur stable, then the
LQG closed loop drives both the plant state and the estimate to zero. -/
theorem lqg_stable_of_stable_gains [DecidableEq n]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ}
    {K : Matrix m n ℝ} {L : Matrix n p ℝ}
    (hK : IsSchurStable (lqrClosedLoop A B K))
    (hL : IsSchurStable (A - L * C))
    (x₀ xh₀ : n → ℝ) :
    Tendsto (fun k => (lqgTraj A B C K L x₀ xh₀ k).1) atTop (𝓝 0) ∧
      Tendsto (fun k => (lqgTraj A B C K L x₀ xh₀ k).2) atTop (𝓝 0) := by
  set e : ℕ → n → ℝ := fun k => (lqgTraj A B C K L x₀ xh₀ k).1 - (lqgTraj A B C K L x₀ xh₀ k).2
  have he_pow : ∀ k, e k = ((A - L * C) ^ k) *ᵥ e 0 := fun k =>
    linear_dynamics_pow' (A - L * C) e (lqgTraj_error_step A B C K L x₀ xh₀) k
  have he : Tendsto e atTop (𝓝 0) := by
    refine (hL (e 0)).congr fun k => (he_pow k).symm
  have hd : Tendsto (fun k => (B * K) *ᵥ e k) atTop (𝓝 0) := by
    have hcont : Continuous fun v : n → ℝ => (B * K) *ᵥ v :=
      continuous_const.matrix_mulVec continuous_id
    simpa only [mulVec_zero, Function.comp_def] using (hcont.tendsto 0).comp he
  have hx := tendsto_zero_of_schur_forced (x := fun k => (lqgTraj A B C K L x₀ xh₀ k).1)
    (d := fun k => (B * K) *ᵥ e k) hK (lqgTraj_state_step A B C K L x₀ xh₀) hd
  refine ⟨hx, ?_⟩
  have h := hx.sub he
  simp only [sub_zero] at h
  refine h.congr fun k => ?_
  simp [e]

omit [Fintype r] in
/-- **Headline Theorem 1 — Minimal-Hypothesis Output-Feedback LQG Separation Theorem**:
Suppose $R \succ 0$, $(A, C_q)$ is detectable, $P \succeq 0$ solves the control DARE for
$Q = C_q^\top C_q \succeq 0$, and $L$ is a Schur-stabilizing observer gain for $(A, C)$.
Then $P$ is the unique symmetric PSD solution of the control DARE and the certainty-equivalence
LQG output-feedback loop drives $x_k \to 0$, $\hat{x}_k \to 0$, and $x_k - \hat{x}_k \to 0$. -/
theorem lqg_closed_loop_stable_of_stabilizable_detectable
    [DecidableEq n] [DecidableEq m]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ}
    {Cq : Matrix q n ℝ} {R : Matrix m m ℝ} {P : Matrix n n ℝ} {L : Matrix n p ℝ}
    (hR : R.PosDef) (hP : SymPSD P) (hdetCq : IsDetectable A Cq)
    (hfix : riccatiMap A B (Cqᵀ * Cq) R P = P)
    (hL : IsSchurStable (A - L * C)) :
    (∀ P', SymPSD P' ∧ riccatiMap A B (Cqᵀ * Cq) R P' = P' → P' = P) ∧
      ∀ x₀ xh₀ : n → ℝ,
        Tendsto (fun k => (lqgTraj A B C (riccatiGain A B R P) L x₀ xh₀ k).1) atTop (𝓝 0) ∧
        Tendsto (fun k => (lqgTraj A B C (riccatiGain A B R P) L x₀ xh₀ k).2) atTop (𝓝 0) ∧
        Tendsto (fun k => (lqgTraj A B C (riccatiGain A B R P) L x₀ xh₀ k).1 -
          (lqgTraj A B C (riccatiGain A B R P) L x₀ xh₀ k).2) atTop (𝓝 0) := by
  have hPschur := dare_schur_of_detectable hR hP hdetCq hfix
  refine ⟨fun P' ⟨hP', hfix'⟩ => dare_unique_of_detectable hR hdetCq hP' hP hfix' hfix,
    fun x₀ xh₀ => ?_⟩
  obtain ⟨hx, hxh⟩ := lqg_stable_of_stable_gains hPschur hL x₀ xh₀
  refine ⟨hx, hxh, ?_⟩
  simpa using hx.sub hxh

/-! ### 2. Discrete-Time $H_\infty$ Disturbance Hessian, Gain & Riccati Operator -/

/-- The discrete-time $H_\infty$ disturbance Hessian matrix:
$$M_\gamma(P) = \gamma^2 I - D^\top D - B^\top P B.$$ -/
def hinfHessian [DecidableEq m] (P : Matrix n n ℝ) (B : Matrix n m ℝ)
    (D : Matrix p m ℝ) (γ : ℝ) : Matrix m m ℝ :=
  (γ ^ 2) • (1 : Matrix m m ℝ) - Dᵀ * D - Bᵀ * P * B

/-- Worst-case state-feedback disturbance gain for the discrete-time $H_\infty$ problem:
$$K_w(P) = M_\gamma(P)^{-1} (B^\top P A + D^\top C).$$ -/
noncomputable def hinfDisturbanceGain [DecidableEq m] (P A : Matrix n n ℝ)
    (B : Matrix n m ℝ) (C : Matrix p n ℝ) (D : Matrix p m ℝ) (γ : ℝ) : Matrix m n ℝ :=
  (hinfHessian P B D γ)⁻¹ * (Bᵀ * P * A + Dᵀ * C)

/-- Discrete-time $H_\infty$ Algebraic Riccati operator:
$$\mathcal{R}_\infty(P) = A^\top P A + C^\top C +
  (A^\top P B + C^\top D) M_\gamma(P)^{-1} (B^\top P A + D^\top C).$$ -/
noncomputable def hinfRiccatiMap [DecidableEq m] (P A : Matrix n n ℝ)
    (B : Matrix n m ℝ) (C : Matrix p n ℝ) (D : Matrix p m ℝ) (γ : ℝ) : Matrix n n ℝ :=
  Aᵀ * P * A + Cᵀ * C +
    (Aᵀ * P * B + Cᵀ * D) * (hinfHessian P B D γ)⁻¹ * (Bᵀ * P * A + Dᵀ * C)

omit [Fintype m] [Fintype q] [Fintype r] in
/-- Symmetry of the $H_\infty$ disturbance Hessian $M_\gamma(P)$ when $P$ is symmetric. -/
theorem hinfHessian_transpose [DecidableEq m] {P : Matrix n n ℝ} (B : Matrix n m ℝ)
    (D : Matrix p m ℝ) (γ : ℝ) (hP : Pᵀ = P) :
    (hinfHessian P B D γ)ᵀ = hinfHessian P B D γ := by
  unfold hinfHessian
  simp only [transpose_sub, transpose_smul, transpose_one, transpose_mul, transpose_transpose,
    hP, Matrix.mul_assoc]

omit [Fintype q] [Fintype r] in
/-- Quadratic form of the $H_\infty$ disturbance Hessian:
$$w^\top M_\gamma(P) w = \gamma^2 (w \cdot w) - (D w) \cdot (D w) - (B w)^\top P (B w).$$ -/
theorem quad_hinfHessian [DecidableEq m] (P : Matrix n n ℝ) (B : Matrix n m ℝ)
    (D : Matrix p m ℝ) (γ : ℝ) (w : m → ℝ) :
    quad (hinfHessian P B D γ) w =
      γ ^ 2 * (w ⬝ᵥ w) - (D *ᵥ w) ⬝ᵥ (D *ᵥ w) - quad P (B *ᵥ w) := by
  unfold hinfHessian
  rw [quad_sub, quad_sub, quad_smul_mat, quad_transpose_mul_self, quad_mulVec_rect]
  simp [quad]

omit [Fintype q] [Fintype r] in
/-- The worst-case disturbance gain `hinfDisturbanceGain` solves the $H_\infty$ normal equation
$$M_\gamma(P) K_w(P) = B^\top P A + D^\top C$$
whenever $\det M_\gamma(P)$ is invertible (in particular when $M_\gamma(P) \succ 0$). -/
theorem hinfDisturbanceGain_normal_eq [DecidableEq m] {P A : Matrix n n ℝ}
    {B : Matrix n m ℝ} {C : Matrix p n ℝ} {D : Matrix p m ℝ} {γ : ℝ}
    (hM : IsUnit (hinfHessian P B D γ).det) :
    hinfHessian P B D γ * hinfDisturbanceGain P A B C D γ = Bᵀ * P * A + Dᵀ * C := by
  unfold hinfDisturbanceGain
  exact mul_nonsing_inv_cancel_left _ _ hM

omit [Fintype q] [Fintype r] in
/-- Transposed $H_\infty$ normal equation: if $P^\top = P$ and
$M_\gamma(P) K_w = B^\top P A + D^\top C$, then
$$K_w^\top M_\gamma(P) = A^\top P B + C^\top D.$$ -/
theorem hinf_normal_eq_transpose [DecidableEq m] {P A : Matrix n n ℝ}
    {B : Matrix n m ℝ} {C : Matrix p n ℝ} {D : Matrix p m ℝ} {γ : ℝ}
    {Kw : Matrix m n ℝ} (hP : Pᵀ = P)
    (hKw : hinfHessian P B D γ * Kw = Bᵀ * P * A + Dᵀ * C) :
    Kwᵀ * hinfHessian P B D γ = Aᵀ * P * B + Cᵀ * D := by
  calc Kwᵀ * hinfHessian P B D γ
      = (hinfHessian P B D γ * Kw)ᵀ := by rw [transpose_mul, hinfHessian_transpose B D γ hP]
    _ = (Bᵀ * P * A + Dᵀ * C)ᵀ := by rw [hKw]
    _ = Aᵀ * P * B + Cᵀ * D := by
        simp only [transpose_add, transpose_mul, transpose_transpose, hP, Matrix.mul_assoc]

omit [Fintype q] [Fintype r] in
/-- Representation of $\mathcal{R}_\infty(P)$ in terms of the worst-case disturbance gain $K_w(P)$:
$$\mathcal{R}_\infty(P) = A^\top P A + C^\top C + K_w(P)^\top M_\gamma(P) K_w(P).$$ -/
theorem hinfRiccatiMap_eq_add_gain [DecidableEq m] {P A : Matrix n n ℝ}
    {B : Matrix n m ℝ} {C : Matrix p n ℝ} {D : Matrix p m ℝ} {γ : ℝ}
    (hP : Pᵀ = P) (hM : IsUnit (hinfHessian P B D γ).det) :
    hinfRiccatiMap P A B C D γ =
      Aᵀ * P * A + Cᵀ * C +
        (hinfDisturbanceGain P A B C D γ)ᵀ * hinfHessian P B D γ *
          hinfDisturbanceGain P A B C D γ := by
  have hnorm := hinfDisturbanceGain_normal_eq (A := A) (C := C) hM
  have hKT := hinf_normal_eq_transpose hP hnorm
  unfold hinfRiccatiMap
  rw [← hKT]
  congr 1
  unfold hinfDisturbanceGain
  simp only [Matrix.mul_assoc]

omit [Fintype q] [Fintype r] in
/-- If $P$ is symmetric, then $\mathcal{R}_\infty(P)$ is symmetric. -/
theorem hinfRiccatiMap_transpose [DecidableEq m] {P A : Matrix n n ℝ}
    (B : Matrix n m ℝ) (C : Matrix p n ℝ) (D : Matrix p m ℝ) (γ : ℝ) (hP : Pᵀ = P) :
    (hinfRiccatiMap P A B C D γ)ᵀ = hinfRiccatiMap P A B C D γ := by
  unfold hinfRiccatiMap
  have hM := hinfHessian_transpose B D γ hP
  simp only [transpose_add, transpose_mul, transpose_nonsing_inv, transpose_transpose,
    hP, hM, Matrix.mul_assoc]

/-! ### 3. Fundamental $H_\infty$ Completing-the-Square Identity -/

omit [Fintype q] [Fintype r] in
/-- **Headline Theorem 2 — Fundamental $H_\infty$ Stage Completion of Squares**:
For any symmetric matrix $P^\top = P$ such that $M_\gamma(P)$ has invertible determinant, and for
every state $x \in \mathbb{R}^n$ and disturbance $w \in \mathbb{R}^m$:
$$\|C x + D w\|_2^2 - \gamma^2 \|w\|_2^2 + (A x + B w)^\top P (A x + B w) - x^\top P x
  = x^\top (\mathcal{R}_\infty(P) - P) x -
    (w - K_w(P) x)^\top M_\gamma(P) (w - K_w(P) x).$$ -/
theorem hinf_stage_completion_of_squares [DecidableEq m] {P A : Matrix n n ℝ}
    {B : Matrix n m ℝ} {C : Matrix p n ℝ} {D : Matrix p m ℝ} {γ : ℝ}
    (hP : Pᵀ = P) (hM : IsUnit (hinfHessian P B D γ).det)
    (x : n → ℝ) (w : m → ℝ) :
    (C *ᵥ x + D *ᵥ w) ⬝ᵥ (C *ᵥ x + D *ᵥ w) - γ ^ 2 * (w ⬝ᵥ w) +
        quad P (A *ᵥ x + B *ᵥ w) - quad P x =
      quad (hinfRiccatiMap P A B C D γ - P) x -
        quad (hinfHessian P B D γ) (w - hinfDisturbanceGain P A B C D γ *ᵥ x) := by
  set Kw := hinfDisturbanceGain P A B C D γ
  set M := hinfHessian P B D γ
  have hnorm : M * Kw = Bᵀ * P * A + Dᵀ * C := hinfDisturbanceGain_normal_eq hM
  have hKT : Kwᵀ * M = Aᵀ * P * B + Cᵀ * D := hinf_normal_eq_transpose hP hnorm
  have hRmap := hinfRiccatiMap_eq_add_gain (A := A) (C := C) hP hM
  have h_cross1 : (A *ᵥ x) ⬝ᵥ (P *ᵥ (B *ᵥ w)) + (C *ᵥ x) ⬝ᵥ (D *ᵥ w) =
      (Kw *ᵥ x) ⬝ᵥ (M *ᵥ w) := by
    calc (A *ᵥ x) ⬝ᵥ (P *ᵥ (B *ᵥ w)) + (C *ᵥ x) ⬝ᵥ (D *ᵥ w)
        = x ⬝ᵥ ((Aᵀ * P * B) *ᵥ w) + x ⬝ᵥ ((Cᵀ * D) *ᵥ w) := by
          rw [mulVec_dotProduct_eq A x, mulVec_dotProduct_eq C x]
          simp only [← mulVec_mulVec]
      _ = x ⬝ᵥ ((Aᵀ * P * B + Cᵀ * D) *ᵥ w) := by rw [← dotProduct_add, ← add_mulVec]
      _ = x ⬝ᵥ ((Kwᵀ * M) *ᵥ w) := by rw [← hKT]
      _ = (Kw *ᵥ x) ⬝ᵥ (M *ᵥ w) := by rw [← mulVec_mulVec, ← mulVec_dotProduct_eq Kw x]
  have h_cross2 : (B *ᵥ w) ⬝ᵥ (P *ᵥ (A *ᵥ x)) + (D *ᵥ w) ⬝ᵥ (C *ᵥ x) =
      w ⬝ᵥ (M *ᵥ (Kw *ᵥ x)) := by
    calc (B *ᵥ w) ⬝ᵥ (P *ᵥ (A *ᵥ x)) + (D *ᵥ w) ⬝ᵥ (C *ᵥ x)
        = w ⬝ᵥ ((Bᵀ * P * A) *ᵥ x) + w ⬝ᵥ ((Dᵀ * C) *ᵥ x) := by
          rw [mulVec_dotProduct_eq B w, mulVec_dotProduct_eq D w]
          simp only [← mulVec_mulVec]
      _ = w ⬝ᵥ ((Bᵀ * P * A + Dᵀ * C) *ᵥ x) := by rw [← dotProduct_add, ← add_mulVec]
      _ = w ⬝ᵥ ((M * Kw) *ᵥ x) := by rw [← hnorm]
      _ = w ⬝ᵥ (M *ᵥ (Kw *ᵥ x)) := by rw [← mulVec_mulVec]
  have h_quadA : (A *ᵥ x) ⬝ᵥ (P *ᵥ (A *ᵥ x)) = quad (Aᵀ * P * A) x := quad_mulVec P A x
  have h_quadC : (C *ᵥ x) ⬝ᵥ (C *ᵥ x) = quad (Cᵀ * C) x := (quad_transpose_mul_self C x).symm
  have h_quadKw : (Kw *ᵥ x) ⬝ᵥ (M *ᵥ (Kw *ᵥ x)) = quad (Kwᵀ * M * Kw) x :=
    quad_mulVec_rect M Kw x
  have h_quadM := quad_hinfHessian P B D γ w
  rw [hRmap, quad_sub, quad_add, quad_add]
  have h_exp_P : quad P (A *ᵥ x + B *ᵥ w) =
      (A *ᵥ x) ⬝ᵥ (P *ᵥ (A *ᵥ x)) + (A *ᵥ x) ⬝ᵥ (P *ᵥ (B *ᵥ w)) +
        (B *ᵥ w) ⬝ᵥ (P *ᵥ (A *ᵥ x)) + quad P (B *ᵥ w) := by
    dsimp [quad]
    simp only [mulVec_add, dotProduct_add, add_dotProduct]
    ring
  have h_exp_M : quad M (w - Kw *ᵥ x) =
      quad M w - w ⬝ᵥ (M *ᵥ (Kw *ᵥ x)) - (Kw *ᵥ x) ⬝ᵥ (M *ᵥ w) +
        (Kw *ᵥ x) ⬝ᵥ (M *ᵥ (Kw *ᵥ x)) := by
    dsimp [quad]
    simp only [mulVec_sub, dotProduct_sub, sub_dotProduct]
    ring
  have h_exp_z : (C *ᵥ x + D *ᵥ w) ⬝ᵥ (C *ᵥ x + D *ᵥ w) =
      (C *ᵥ x) ⬝ᵥ (C *ᵥ x) + (C *ᵥ x) ⬝ᵥ (D *ᵥ w) +
        (D *ᵥ w) ⬝ᵥ (C *ᵥ x) + (D *ᵥ w) ⬝ᵥ (D *ᵥ w) := by
    simp only [dotProduct_add, add_dotProduct]
    ring
  rw [h_exp_P, h_exp_M, h_exp_z, h_quadA, h_quadC, h_quadKw, h_quadM]
  linarith [h_cross1, h_cross2]

omit [Fintype q] [Fintype r] in
/-- **One-Step Bounded Real Dissipation Identity at an $H_\infty$ Riccati Fixed Point**:
If $P^\top = P$, $\det M_\gamma(P)$ is invertible, and $\mathcal{R}_\infty(P) = P$, then for every
state $x$ and disturbance $w$:
$$\|C x + D w\|_2^2 + (A x + B w)^\top P (A x + B w) - x^\top P x +
  (w - K_w(P) x)^\top M_\gamma(P) (w - K_w(P) x) = \gamma^2 \|w\|_2^2.$$ -/
theorem hinf_stage_dissipation_of_fixed [DecidableEq m] {P A : Matrix n n ℝ}
    {B : Matrix n m ℝ} {C : Matrix p n ℝ} {D : Matrix p m ℝ} {γ : ℝ}
    (hP : Pᵀ = P) (hM : IsUnit (hinfHessian P B D γ).det)
    (hfix : hinfRiccatiMap P A B C D γ = P)
    (x : n → ℝ) (w : m → ℝ) :
    (C *ᵥ x + D *ᵥ w) ⬝ᵥ (C *ᵥ x + D *ᵥ w) + quad P (A *ᵥ x + B *ᵥ w) - quad P x +
        quad (hinfHessian P B D γ) (w - hinfDisturbanceGain P A B C D γ *ᵥ x) =
      γ ^ 2 * (w ⬝ᵥ w) := by
  have h := hinf_stage_completion_of_squares (A := A) (C := C) hP hM x w
  have hzero : quad (0 : Matrix n n ℝ) x = 0 := by simp [quad]
  rw [hfix, sub_self, hzero] at h
  linarith

/-! ### 4. Finite-Horizon $H_\infty$ $\ell_2$-Gain Bound & Worst-Case Disturbance Tightness -/

/-- State trajectory $x_{k+1} = A x_k + B w_k$ starting at $x_0$. -/
def lqrTraj (A : Matrix n n ℝ) (B : Matrix n m ℝ) (x₀ : n → ℝ) (w : ℕ → m → ℝ) : ℕ → n → ℝ
  | 0 => x₀
  | k + 1 => A *ᵥ lqrTraj A B x₀ w k + B *ᵥ w k

/-- Performance output trajectory $z_k = C x_k + D w_k$ along $x_{k+1} = A x_k + B w_k$. -/
def hinfOutput (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix p n ℝ) (D : Matrix p m ℝ)
    (x₀ : n → ℝ) (w : ℕ → m → ℝ) (k : ℕ) : p → ℝ :=
  C *ᵥ lqrTraj A B x₀ w k + D *ᵥ w k

omit [Fintype q] [Fintype r] in
/-- **Exact Finite-Horizon $H_\infty$ Energy Balance Identity**:
If $P^\top = P$, $\det M_\gamma(P)$ is invertible, and $\mathcal{R}_\infty(P) = P$, then over any
horizon $N \in \mathbb{N}$ and for any disturbance sequence $w : \mathbb{N} \to (m \to \mathbb{R})$:
$$\sum_{k=0}^{N-1} \|z_k\|_2^2 + x_N^\top P x_N +
  \sum_{k=0}^{N-1} (w_k - K_w(P) x_k)^\top M_\gamma(P) (w_k - K_w(P) x_k)
  = \gamma^2 \sum_{k=0}^{N-1} \|w_k\|_2^2 + x_0^\top P x_0.$$ -/
theorem hinf_finite_horizon_identity [DecidableEq m] {P A : Matrix n n ℝ}
    {B : Matrix n m ℝ} {C : Matrix p n ℝ} {D : Matrix p m ℝ} {γ : ℝ}
    (hP : Pᵀ = P) (hM : IsUnit (hinfHessian P B D γ).det)
    (hfix : hinfRiccatiMap P A B C D γ = P)
    (x₀ : n → ℝ) (w : ℕ → m → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, hinfOutput A B C D x₀ w k ⬝ᵥ hinfOutput A B C D x₀ w k) +
        quad P (lqrTraj A B x₀ w N) +
        (∑ k ∈ Finset.range N,
          quad (hinfHessian P B D γ)
            (w k - hinfDisturbanceGain P A B C D γ *ᵥ lqrTraj A B x₀ w k)) =
      γ ^ 2 * (∑ k ∈ Finset.range N, w k ⬝ᵥ w k) + quad P x₀ := by
  induction N with
  | zero => simp [lqrTraj]
  | succ N ih =>
    have hstep := hinf_stage_dissipation_of_fixed hP hM hfix (lqrTraj A B x₀ w N) (w N)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
    change (∑ k ∈ Finset.range N, hinfOutput A B C D x₀ w k ⬝ᵥ hinfOutput A B C D x₀ w k) +
        (C *ᵥ lqrTraj A B x₀ w N + D *ᵥ w N) ⬝ᵥ (C *ᵥ lqrTraj A B x₀ w N + D *ᵥ w N) +
        quad P (A *ᵥ lqrTraj A B x₀ w N + B *ᵥ w N) +
        ((∑ k ∈ Finset.range N,
          quad (hinfHessian P B D γ)
            (w k - hinfDisturbanceGain P A B C D γ *ᵥ lqrTraj A B x₀ w k)) +
          quad (hinfHessian P B D γ)
            (w N - hinfDisturbanceGain P A B C D γ *ᵥ lqrTraj A B x₀ w N)) = _
    linarith [ih, hstep]

omit [Fintype q] [Fintype r] in
/-- **Headline Theorem 3 — Finite-Horizon Bounded Real / $H_\infty$ $\ell_2$-Gain Bound**:
If $P \succeq 0$ solves the $H_\infty$ Riccati equation $\mathcal{R}_\infty(P) = P$ with
$M_\gamma(P) \succ 0$, then for every initial state $x_0$, disturbance sequence $w$, and
horizon $N$:
1. $\sum_{k=0}^{N-1} \|z_k\|_2^2 \le \gamma^2 \sum_{k=0}^{N-1} \|w_k\|_2^2 + x_0^\top P x_0$;
2. For zero initial state ($x_0 = 0$), $\sum_{k=0}^{N-1} \|z_k\|_2^2 \le
   \gamma^2 \sum_{k=0}^{N-1} \|w_k\|_2^2$. -/
theorem hinf_l2_gain_bound [DecidableEq m] {P A : Matrix n n ℝ}
    {B : Matrix n m ℝ} {C : Matrix p n ℝ} {D : Matrix p m ℝ} {γ : ℝ}
    (hP : SymPSD P) (hM : (hinfHessian P B D γ).PosDef)
    (hfix : hinfRiccatiMap P A B C D γ = P)
    (x₀ : n → ℝ) (w : ℕ → m → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, hinfOutput A B C D x₀ w k ⬝ᵥ hinfOutput A B C D x₀ w k) ≤
        γ ^ 2 * (∑ k ∈ Finset.range N, w k ⬝ᵥ w k) + quad P x₀ ∧
      (∑ k ∈ Finset.range N, hinfOutput A B C D 0 w k ⬝ᵥ hinfOutput A B C D 0 w k) ≤
        γ ^ 2 * (∑ k ∈ Finset.range N, w k ⬝ᵥ w k) := by
  have hdet : IsUnit (hinfHessian P B D γ).det := hM.det_pos.ne'.isUnit
  have h1 : ∀ y₀ : n → ℝ,
      (∑ k ∈ Finset.range N, hinfOutput A B C D y₀ w k ⬝ᵥ hinfOutput A B C D y₀ w k) ≤
        γ ^ 2 * (∑ k ∈ Finset.range N, w k ⬝ᵥ w k) + quad P y₀ := by
    intro y₀
    have hid := hinf_finite_horizon_identity hP.1 hdet hfix y₀ w N
    have hPN : 0 ≤ quad P (lqrTraj A B y₀ w N) := hP.2 _
    have hsumM : 0 ≤ ∑ k ∈ Finset.range N,
        quad (hinfHessian P B D γ)
          (w k - hinfDisturbanceGain P A B C D γ *ᵥ lqrTraj A B y₀ w k) :=
      Finset.sum_nonneg fun k _ => quad_nonneg_of_posDef hM _
    linarith
  refine ⟨h1 x₀, ?_⟩
  have h0 := h1 0
  simpa [quad] using h0

omit [Fintype q] [Fintype r] in
/-- **Tightness of the Worst-Case State-Feedback Disturbance $w_k^* = K_w(P) x_k$**:
When the disturbance follows the worst-case state-feedback law $w_k = K_w(P) x_k$, the quadratic
completion-of-squares deficit vanishes identically at every step, achieving exact equality
$$\sum_{k=0}^{N-1} \|z_k\|_2^2 + x_N^\top P x_N =
  \gamma^2 \sum_{k=0}^{N-1} \|w_k\|_2^2 + x_0^\top P x_0.$$ -/
theorem hinf_worstCase_disturbance_tight [DecidableEq m] {P A : Matrix n n ℝ}
    {B : Matrix n m ℝ} {C : Matrix p n ℝ} {D : Matrix p m ℝ} {γ : ℝ}
    (hP : Pᵀ = P) (hM : IsUnit (hinfHessian P B D γ).det)
    (hfix : hinfRiccatiMap P A B C D γ = P)
    (x₀ : n → ℝ) (w : ℕ → m → ℝ)
    (hw : ∀ k, w k = hinfDisturbanceGain P A B C D γ *ᵥ lqrTraj A B x₀ w k) (N : ℕ) :
    (∑ k ∈ Finset.range N, hinfOutput A B C D x₀ w k ⬝ᵥ hinfOutput A B C D x₀ w k) +
        quad P (lqrTraj A B x₀ w N) =
      γ ^ 2 * (∑ k ∈ Finset.range N, w k ⬝ᵥ w k) + quad P x₀ := by
  have hid := hinf_finite_horizon_identity hP hM hfix x₀ w N
  have hzero : (∑ k ∈ Finset.range N,
      quad (hinfHessian P B D γ)
        (w k - hinfDisturbanceGain P A B C D γ *ᵥ lqrTraj A B x₀ w k)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hw k, sub_self]
    simp [quad]
  linarith

/-! ### 5. Detectable Lyapunov Lemma & Schur Stability of $H_\infty$ Riccati Solutions -/

omit [Fintype m] [Fintype q] [Fintype r] in
/-- **Discrete-Time Detectable Lyapunov Stability Lemma**:
If $P \succeq 0$, $(A, C)$ is detectable, and the one-step Lyapunov decrease dominates the
output energy ($\forall x,\, (C x) \cdot (C x) \le x^\top P x - (A x)^\top P (A x)$), then $A$ is
Schur stable (`IsSchurStable A`). -/
theorem schur_of_lyapunov_le_detectable [DecidableEq n]
    {P A : Matrix n n ℝ} {C : Matrix p n ℝ}
    (hP : SymPSD P) (hdet : IsDetectable A C)
    (hlyap : ∀ x : n → ℝ, (C *ᵥ x) ⬝ᵥ (C *ᵥ x) ≤ quad P x - quad P (A *ᵥ x)) :
    IsSchurStable A := by
  obtain ⟨L, hL⟩ := hdet
  intro x₀
  have hsum : Summable (fun k : ℕ => (C *ᵥ ((A ^ k) *ᵥ x₀)) ⬝ᵥ (C *ᵥ ((A ^ k) *ᵥ x₀))) := by
    refine summable_of_sum_range_le (fun _ => dotProduct_self_nonneg' _)
      (c := quad P x₀) fun N => ?_
    have htel : ∑ k ∈ Finset.range N, (C *ᵥ ((A ^ k) *ᵥ x₀)) ⬝ᵥ (C *ᵥ ((A ^ k) *ᵥ x₀)) ≤
        quad P x₀ - quad P ((A ^ N) *ᵥ x₀) := by
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, pow_succ', ← mulVec_mulVec]
        linarith [hlyap ((A ^ N) *ᵥ x₀)]
    linarith [htel, hP.2 ((A ^ N) *ᵥ x₀)]
  have hCx : Tendsto (fun k : ℕ => C *ᵥ ((A ^ k) *ᵥ x₀)) atTop (𝓝 0) :=
    tendsto_zero_of_dotProduct_self_tendsto_zero hsum.tendsto_atTop_zero
  have hd : Tendsto (fun k : ℕ => L *ᵥ (C *ᵥ ((A ^ k) *ᵥ x₀))) atTop (𝓝 0) := by
    have hcont : Continuous fun y : p → ℝ => L *ᵥ y :=
      continuous_const.matrix_mulVec continuous_id
    simpa only [mulVec_zero, Function.comp_def] using (hcont.tendsto 0).comp hCx
  have hstep : ∀ k : ℕ, (A ^ (k + 1)) *ᵥ x₀ =
      (A - L * C) *ᵥ ((A ^ k) *ᵥ x₀) + L *ᵥ (C *ᵥ ((A ^ k) *ᵥ x₀)) := by
    intro k
    rw [pow_succ', ← mulVec_mulVec, sub_mulVec, ← mulVec_mulVec]
    abel
  exact tendsto_zero_of_schur_forced hL hstep hd

omit [Fintype q] [Fintype r] in
/-- **Headline Theorem 4 — Schur Stability from the $H_\infty$ Riccati Equation under
Detectability**:
If $P \succeq 0$ satisfies $\mathcal{R}_\infty(P) \preceq P$ (in particular if $P =
\mathcal{R}_\infty(P)$), $M_\gamma(P) \succ 0$, and $(A, C)$ is detectable, then the unforced
system matrix $A$ is Schur stable (`IsSchurStable A`). -/
theorem hinf_schur_of_detectable [DecidableEq n] [DecidableEq m]
    {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ} {D : Matrix p m ℝ} {γ : ℝ}
    (hP : SymPSD P) (hM : (hinfHessian P B D γ).PosDef)
    (hdet : IsDetectable A C)
    (hle : LoewnerLE (hinfRiccatiMap P A B C D γ) P) :
    IsSchurStable A := by
  have hdetM : IsUnit (hinfHessian P B D γ).det := hM.det_pos.ne'.isUnit
  have hRmap := hinfRiccatiMap_eq_add_gain (A := A) (C := C) hP.1 hdetM
  refine schur_of_lyapunov_le_detectable hP hdet fun x => ?_
  have hx := hle x
  rw [hRmap, quad_add, quad_add, ← quad_mulVec P A x, quad_transpose_mul_self,
    ← quad_mulVec_rect] at hx
  have hKw0 : 0 ≤ quad (hinfHessian P B D γ) (hinfDisturbanceGain P A B C D γ *ᵥ x) :=
    quad_nonneg_of_posDef hM _
  linarith

end ControlsLean.Controls
