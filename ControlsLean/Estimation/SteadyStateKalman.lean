/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.DAREUniqueness
import ControlsLean.Controls.Observer

/-!
# The Steady-State Kalman Filter, by Control–Estimation Duality

For the stochastic LTI model
$$x_{k+1} = A x_k + w_k, \qquad y_k = C x_k + v_k, \qquad
  \operatorname{Cov}(w) = W, \quad \operatorname{Cov}(v) = V,$$
the one-step predicted error covariance of the Kalman filter evolves by the filtering Riccati map
$$\mathcal{K}(\Sigma) = W + A \Sigma A^\top
  - A \Sigma C^\top (V + C \Sigma C^\top)^{-1} C \Sigma A^\top,$$
with predictor gain $L(\Sigma) = A \Sigma C^\top (V + C \Sigma C^\top)^{-1}$.

**Duality**: $\mathcal{K}$ is exactly the LQR Riccati map for $(A^\top, C^\top, W, V)$. So the
existence and uniqueness theory of `DAREExistence.lean`, `SchurLyapunov.lean` and
`DAREUniqueness.lean` carries over to estimation once stabilizability of $(A^\top, C^\top)$ is
read as **detectability** of $(A, C)$.

## Main results

- `kalmanMap_standard_form`: the dual Riccati map is the filtering Riccati recursion above.
- `kalmanGain_eq`: the dual gain is the predictor Kalman gain
  $A \Sigma C^\top (V + C\Sigma C^\top)^{-1}$.
- `schur_transpose`: Schur stability is invariant under transposition.
- `kalman_steady_state`: if $V \succ 0$, $W \succ 0$ and $(A, C)$ is detectable, the filtering
  ARE has a **unique** PSD solution $\Sigma \succ 0$. Covariance iteration from $\Sigma_0 = 0$
  converges to it, and the steady-state error dynamics $A - L(\Sigma) C$ are Schur stable.
- `kalman_observer_error_tendsto_zero`: run as a Luenberger observer (`Observer.lean`), the
  steady-state Kalman predictor drives the estimation error to zero for **every** input sequence
  and every initial condition.
-/

namespace ControlsLean.Estimation

open Matrix Filter Topology ControlsLean.Controls ControlsLean.Tactics

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq p]

/-- Filtering Riccati map $\mathcal{K}(\Sigma)$, defined as the dual LQR Riccati map. -/
noncomputable def kalmanMap (A : Matrix n n ℝ) (C : Matrix p n ℝ) (W : Matrix n n ℝ)
    (V : Matrix p p ℝ) (Sig : Matrix n n ℝ) : Matrix n n ℝ :=
  riccatiMap Aᵀ Cᵀ W V Sig

/-- Predictor Kalman gain $L(\Sigma)$, the transpose of the dual LQR gain. -/
noncomputable def kalmanGain (A : Matrix n n ℝ) (C : Matrix p n ℝ) (V : Matrix p p ℝ)
    (Sig : Matrix n n ℝ) : Matrix n p ℝ :=
  (riccatiGain Aᵀ Cᵀ V Sig)ᵀ

/-- Covariance iteration $\Sigma_0 = 0$, $\Sigma_{k+1} = \mathcal{K}(\Sigma_k)$. -/
noncomputable def kalmanIter (A : Matrix n n ℝ) (C : Matrix p n ℝ) (W : Matrix n n ℝ)
    (V : Matrix p p ℝ) : ℕ → Matrix n n ℝ :=
  riccatiIter Aᵀ Cᵀ W V

omit [Fintype p] [DecidableEq p] in
/-- The innovation covariance $V + C \Sigma C^\top$ is the dual LQR Hessian. -/
theorem lqrHessian_dual (Sig : Matrix n n ℝ) (C : Matrix p n ℝ) (V : Matrix p p ℝ) :
    lqrHessian Sig Cᵀ V = V + C * Sig * Cᵀ := by
  simp [lqrHessian]

/-- **Filtering Riccati recursion in standard form**: for symmetric PSD $\Sigma$,
$\mathcal{K}(\Sigma) = W + A\Sigma A^\top
  - A\Sigma C^\top (V + C\Sigma C^\top)^{-1} C\Sigma A^\top$. -/
theorem kalmanMap_standard_form {A : Matrix n n ℝ} {C : Matrix p n ℝ} {W : Matrix n n ℝ}
    {V : Matrix p p ℝ} (hV : V.PosDef) {Sig : Matrix n n ℝ} (hSig : SymPSD Sig) :
    kalmanMap A C W V Sig =
      W + A * Sig * Aᵀ - A * Sig * Cᵀ * (V + C * Sig * Cᵀ)⁻¹ * (C * Sig * Aᵀ) := by
  unfold kalmanMap
  rw [riccatiMap_standard_form hV hSig, lqrHessian_dual]
  simp only [transpose_transpose]

/-- **Predictor Kalman gain**: for symmetric $\Sigma$ and $V$,
$L(\Sigma) = A \Sigma C^\top (V + C \Sigma C^\top)^{-1}$. -/
theorem kalmanGain_eq {A : Matrix n n ℝ} {C : Matrix p n ℝ} {V : Matrix p p ℝ}
    (hV : Vᵀ = V) {Sig : Matrix n n ℝ} (hSig : Sigᵀ = Sig) :
    kalmanGain A C V Sig = A * Sig * Cᵀ * (V + C * Sig * Cᵀ)⁻¹ := by
  unfold kalmanGain riccatiGain
  rw [lqrHessian_dual, transpose_mul, transpose_nonsing_inv]
  have hS : (V + C * Sig * Cᵀ)ᵀ = V + C * Sig * Cᵀ := by
    simp only [transpose_add, transpose_mul, transpose_transpose, hV, hSig, Matrix.mul_assoc]
  rw [hS]
  simp only [transpose_mul, transpose_transpose, hSig, Matrix.mul_assoc]

omit [Fintype n] [DecidableEq p] in
/-- The dual closed loop is the transpose of the estimation error dynamics:
$A^\top - C^\top L^\top = (A - L C)^\top$. -/
theorem lqrClosedLoop_dual (A : Matrix n n ℝ) (C : Matrix p n ℝ) (L : Matrix n p ℝ) :
    lqrClosedLoop Aᵀ Cᵀ Lᵀ = (A - L * C)ᵀ := by
  simp [lqrClosedLoop, transpose_sub, transpose_mul]

/-- **Schur stability is invariant under transposition**: if $M^k x \to 0$ for every $x$, then
$(M^\top)^k x \to 0$ for every $x$. -/
theorem schur_transpose [DecidableEq n] {M : Matrix n n ℝ}
    (h : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (M ^ k) *ᵥ x) atTop (𝓝 0)) :
    ∀ x : n → ℝ, Tendsto (fun k : ℕ => (Mᵀ ^ k) *ᵥ x) atTop (𝓝 0) := by
  have hmat : Tendsto (fun k : ℕ => M ^ k) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have h1 := tendsto_pi_nhds.1 (h (Pi.single j 1)) i
    simpa [mulVec_single_one] using h1
  have hT : Tendsto (fun k : ℕ => (M ^ k)ᵀ) atTop (𝓝 0) := by
    simpa using tendsto_transpose hmat
  intro x
  have hcont : Continuous fun X : Matrix n n ℝ => X *ᵥ x :=
    continuous_id.matrix_mulVec continuous_const
  have h2 := (hcont.tendsto 0).comp hT
  simp only [zero_mulVec] at h2
  refine h2.congr fun k => ?_
  simp [Function.comp_apply, Matrix.transpose_pow]

/-- **Steady-state Kalman filter: existence, uniqueness, convergence and stability.**
Let $V \succ 0$, $W \succ 0$, and let $(A, C)$ be detectable, i.e. some observer gain $L_0$ makes
$(A - L_0 C)^k x \to 0$ for every $x$. Then there is a unique symmetric PSD solution $\Sigma$ of the
filtering ARE $\Sigma = \mathcal{K}(\Sigma)$. Moreover:
- $\Sigma \succ 0$;
- $\Sigma$ is given in standard form by
  $\Sigma = W + A\Sigma A^\top - A\Sigma C^\top (V + C\Sigma C^\top)^{-1} C\Sigma A^\top$;
- covariance iteration from $\Sigma_0 = 0$ converges to $\Sigma$;
- the steady-state error dynamics $A - L(\Sigma) C$ are Schur stable. -/
theorem kalman_steady_state [DecidableEq n] {A : Matrix n n ℝ} {C : Matrix p n ℝ}
    {W : Matrix n n ℝ} {V : Matrix p p ℝ} (hV : V.PosDef) (hW : W.PosDef) (L₀ : Matrix n p ℝ)
    (hL₀ : ∀ x : n → ℝ, Tendsto (fun k : ℕ => ((A - L₀ * C) ^ k) *ᵥ x) atTop (𝓝 0)) :
    ∃ Sig : Matrix n n ℝ, (SymPSD Sig ∧ kalmanMap A C W V Sig = Sig) ∧
      (∀ Sig', SymPSD Sig' ∧ kalmanMap A C W V Sig' = Sig' → Sig' = Sig) ∧
      Sig.PosDef ∧
      Sig = W + A * Sig * Aᵀ - A * Sig * Cᵀ * (V + C * Sig * Cᵀ)⁻¹ * (C * Sig * Aᵀ) ∧
      Tendsto (kalmanIter A C W V) atTop (𝓝 Sig) ∧
      ∀ x : n → ℝ, Tendsto (fun k : ℕ => ((A - kalmanGain A C V Sig * C) ^ k) *ᵥ x)
        atTop (𝓝 0) := by
  have hdual : ∀ x : n → ℝ,
      Tendsto (fun k : ℕ => (lqrClosedLoop Aᵀ Cᵀ L₀ᵀ ^ k) *ᵥ x) atTop (𝓝 0) := by
    rw [lqrClosedLoop_dual]
    exact schur_transpose hL₀
  obtain ⟨Sig, ⟨hSig, hfix⟩, huniq, hpd, hT, hstab⟩ :=
    lqr_existsUnique_of_stabilizable (A := Aᵀ) (B := Cᵀ) hV hW L₀ᵀ hdual
  refine ⟨Sig, ⟨hSig, hfix⟩, huniq, hpd, ?_, hT, ?_⟩
  · conv_lhs => rw [← hfix]
    exact kalmanMap_standard_form hV hSig
  · have hstab' := schur_transpose hstab
    have hK : riccatiGain Aᵀ Cᵀ V Sig = (kalmanGain A C V Sig)ᵀ := by
      simp [kalmanGain]
    rw [hK, lqrClosedLoop_dual, transpose_transpose] at hstab'
    exact hstab'

/-- **Steady-state Kalman predictor as an observer**: with the steady-state gain
$L = L(\Sigma)$, the Luenberger observer of `Observer.lean` drives the estimation error to zero
for every initial state, initial estimate and input sequence. -/
theorem kalman_observer_error_tendsto_zero [DecidableEq n] {m : Type*} [Fintype m]
    {A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ}
    {W : Matrix n n ℝ} {V : Matrix p p ℝ} (hV : V.PosDef) (hW : W.PosDef) (L₀ : Matrix n p ℝ)
    (hL₀ : ∀ x : n → ℝ, Tendsto (fun k : ℕ => ((A - L₀ * C) ^ k) *ᵥ x) atTop (𝓝 0)) :
    ∃ Sig : Matrix n n ℝ, Sig.PosDef ∧ kalmanMap A C W V Sig = Sig ∧
      ∀ (x₀ x_hat₀ : n → ℝ) (u : ℕ → m → ℝ),
        Tendsto (errorTraj A B C (kalmanGain A C V Sig) x₀ x_hat₀ u) atTop (𝓝 0) := by
  obtain ⟨Sig, ⟨-, hfix⟩, -, hpd, -, -, hstab⟩ := kalman_steady_state hV hW L₀ hL₀
  refine ⟨Sig, hpd, hfix, fun x₀ x_hat₀ u => ?_⟩
  refine (hstab (errorTraj A B C (kalmanGain A C V Sig) x₀ x_hat₀ u 0)).congr fun k => ?_
  exact (observer_error_pow A B C _ x₀ x_hat₀ u k).symm

end ControlsLean.Estimation
