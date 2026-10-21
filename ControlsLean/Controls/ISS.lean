/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.SchurLyapunov
import ControlsLean.Controls.LQG

/-!
# Discrete-Time Input-to-State Stability (ISS) and Quadratic Perturbation Envelopes

This module formalizes discrete-time **Input-to-State Stability (ISS)** (Roadmap §4.3),
connecting disturbed Lyapunov dissipation inequalities to finite-horizon telescoping
envelopes, forward-invariant sublevel sets, ultimate boundedness, converging-input
asymptotic stability, and explicit quadratic ISS certificates for Schur-stable linear
systems via the matrix Peter–Paul (Young) inequality.

## Main Results

1. **Discrete-Time ISS Telescoping & Sublevel Invariance**:
   - `iss_lyapunov_convolution_bound`: Exact discrete variation-of-constants inequality
     $$V(x_N) \le \rho^N V(x_0) + \sum_{k=0}^{N-1} \rho^{N - 1 - k} \gamma(\|w_k\|).$$
   - `iss_lyapunov_step_bound`: For bounded disturbances $\gamma(\|w_k\|) \le d$,
     $$V(x_N) \le \rho^N V(x_0) + d \frac{1 - \rho^N}{1 - \rho}.$$
   - `iss_lyapunov_uniform_bound`: Uniform envelope $V(x_N) \le \rho^N V(x_0) + \frac{d}{1 - \rho}$.
   - `iss_invariant_sublevel`: Forward invariance of the ISS sublevel ball
     $\{x \mid V(x) \le \frac{d}{1 - \rho}\}$.
   - `iss_ultimate_bound`: Asymptotic ultimate bound
     $\forall \varepsilon > 0, \exists K, \forall N \ge K, V(x_N) \le \frac{d}{1 - \rho} + \varepsilon$.

2. **Converging-Disturbance Asymptotic Stability**:
   - `tendsto_zero_of_linear_dissipation`: If $0 \le a_k$, $a_{k+1} \le \rho a_k + d_k$ with
     $0 \le \rho < 1$, and $d_k \to 0$, then $a_k \to 0$.
   - `iss_tendsto_zero_of_disturbance_tendsto_zero`: Any non-negative ISS Lyapunov function
     along a disturbed trajectory with vanishing disturbance $d_k \to 0$ converges to $0$.

3. **Matrix Peter–Paul Inequality & Quadratic ISS for Schur-Stable Systems**:
   - `quad_add_peter_paul_identity`: Exact completion-of-squares identity for symmetric matrices:
     $$\operatorname{quad} P (u + v) + \varepsilon^{-1} \operatorname{quad} P (\varepsilon u - v)
       = (1 + \varepsilon) \operatorname{quad} P u + (1 + \varepsilon^{-1}) \operatorname{quad} P v.$$
   - `quad_add_le_peter_paul`: Matrix Peter–Paul / Young inequality for `SymPSD P` and $\varepsilon > 0$.
   - `quad_iss_of_stein`: Explicit quadratic ISS step bound for solutions of $A^\top P A - P = -Q$
     with $Q \succeq \alpha P$.
   - `schur_quadratic_iss`: Every Schur-stable matrix $A$ admits a positive definite quadratic
     ISS Lyapunov function $V(x) = x^\top P x$ with contraction rate $\rho \in [0, 1)$ and
     quadratic disturbance gain $\gamma > 0$.

## References

- E. D. Sontag, *Smooth stabilization implies coprime factorization*, IEEE TAC 34 (1989), 435–443.
- Z.-P. Jiang, Y. Wang, *Input-to-state stability for discrete-time nonlinear systems*,
  Automatica 37 (2001), 857–869.
-/

namespace ControlsLean.Controls

open Matrix Filter Topology BigOperators ControlsLean.Tactics

/-! ### 1. Discrete-Time ISS Telescoping Envelopes -/

section ScalarISS

variable {X W : Type*}

/-- One-step scalar recursion bound: if $a_{k+1} \le \rho a_k + d_k$ and $\rho \ge 0$, then
$$a_N \le \rho^N a_0 + \sum_{k=0}^{N-1} \rho^{N - 1 - k} d_k.$$ -/
theorem scalar_dissipation_convolution_bound {a d : ℕ → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hstep : ∀ k, a (k + 1) ≤ ρ * a k + d k) :
    ∀ N : ℕ, a N ≤ ρ ^ N * a 0 + ∑ k ∈ Finset.range N, ρ ^ (N - 1 - k) * d k
  | 0 => by simp
  | N + 1 => by
    have ih := scalar_dissipation_convolution_bound hρ0 hstep N
    have hmul : ρ * a N ≤ ρ * (ρ ^ N * a 0 + ∑ k ∈ Finset.range N, ρ ^ (N - 1 - k) * d k) :=
      mul_le_mul_of_nonneg_left ih hρ0
    rw [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    have hsum_eq :
        ρ * ∑ k ∈ Finset.range N, ρ ^ (N - 1 - k) * d k =
          ∑ k ∈ Finset.range N, ρ ^ (N + 1 - 1 - k) * d k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_lt : k < N := Finset.mem_range.1 hk
      have hexp : N + 1 - 1 - k = (N - 1 - k) + 1 := by omega
      rw [hexp, pow_succ']
      ring
    calc a (N + 1) ≤ ρ * a N + d N := hstep N
      _ ≤ ρ * (ρ ^ N * a 0 + ∑ k ∈ Finset.range N, ρ ^ (N - 1 - k) * d k) + d N := by linarith
      _ = ρ ^ (N + 1) * a 0 + (ρ * ∑ k ∈ Finset.range N, ρ ^ (N - 1 - k) * d k + d N) := by
          rw [pow_succ']
          ring
      _ = ρ ^ (N + 1) * a 0 +
            (∑ k ∈ Finset.range N, ρ ^ (N + 1 - 1 - k) * d k + d N) := by rw [hsum_eq]

/-- Exact finite-horizon ISS convolution envelope for a disturbed discrete-time system
$x_{k+1} = f(x_k, w_k)$ with Lyapunov function $V : X \to \mathbb{R}$ and disturbance gain
$\gamma : W \to \mathbb{R}$:
$$V(x_N) \le \rho^N V(x_0) + \sum_{k=0}^{N-1} \rho^{N - 1 - k} \gamma(w_k).$$ -/
theorem iss_lyapunov_convolution_bound (V : X → ℝ) (f : X → W → X) (γ : W → ℝ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hdiss : ∀ x w, V (f x w) ≤ ρ * V x + γ w)
    (x : ℕ → X) (w : ℕ → W) (htraj : ∀ k, x (k + 1) = f (x k) (w k)) (N : ℕ) :
    V (x N) ≤ ρ ^ N * V (x 0) + ∑ k ∈ Finset.range N, ρ ^ (N - 1 - k) * γ (w k) := by
  refine scalar_dissipation_convolution_bound (a := fun k => V (x k)) (d := fun k => γ (w k))
    hρ0 (fun k => ?_) N
  rw [htraj k]
  exact hdiss (x k) (w k)

/-- **Exact Finite-Horizon Telescoping ISS Envelope**:
For any trajectory $x_{k+1} = f(x_k, w_k)$ satisfying $V(f(x, w)) \le \rho V(x) + \gamma(w)$
with $0 \le \rho < 1$ and bounded disturbance $\forall k < N, \gamma(w_k) \le d$,
$$V(x_N) \le \rho^N V(x_0) + d \frac{1 - \rho^N}{1 - \rho}.$$ -/
theorem iss_lyapunov_step_bound (V : X → ℝ) (f : X → W → X) (γ : W → ℝ) {ρ d : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiss : ∀ x w, V (f x w) ≤ ρ * V x + γ w)
    (x : ℕ → X) (w : ℕ → W) (htraj : ∀ k, x (k + 1) = f (x k) (w k))
    (N : ℕ) (hd : ∀ k < N, γ (w k) ≤ d) :
    V (x N) ≤ ρ ^ N * V (x 0) + d * ((1 - ρ ^ N) / (1 - ρ)) := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    have ih' := ih (fun k hk => hd k (Nat.lt_succ_of_lt hk))
    have hstep : V (x (N + 1)) ≤ ρ * V (x N) + γ (w N) := by
      rw [htraj N]
      exact hdiss (x N) (w N)
    have hdN : γ (w N) ≤ d := hd N (Nat.lt_succ_self N)
    have hρ_sub : 0 < 1 - ρ := sub_pos.2 hρ1
    have hρ_ne : 1 - ρ ≠ 0 := hρ_sub.ne'
    have h_alg :
        ρ * (ρ ^ N * V (x 0) + d * ((1 - ρ ^ N) / (1 - ρ))) + d =
          ρ ^ (N + 1) * V (x 0) + d * ((1 - ρ ^ (N + 1)) / (1 - ρ)) := by
      rw [pow_succ']
      field_simp [hρ_ne]
      ring
    calc V (x (N + 1)) ≤ ρ * V (x N) + γ (w N) := hstep
      _ ≤ ρ * (ρ ^ N * V (x 0) + d * ((1 - ρ ^ N) / (1 - ρ))) + d := by
          exact add_le_add (mul_le_mul_of_nonneg_left ih' hρ0) hdN
      _ = ρ ^ (N + 1) * V (x 0) + d * ((1 - ρ ^ (N + 1)) / (1 - ρ)) := h_alg

/-- **Uniform ISS Trajectory Envelope**:
When $d \ge 0$ and $\gamma(w_k) \le d$ for all $k < N$,
$$V(x_N) \le \rho^N V(x_0) + \frac{d}{1 - \rho}.$$ -/
theorem iss_lyapunov_uniform_bound (V : X → ℝ) (f : X → W → X) (γ : W → ℝ) {ρ d : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hd0 : 0 ≤ d)
    (hdiss : ∀ x w, V (f x w) ≤ ρ * V x + γ w)
    (x : ℕ → X) (w : ℕ → W) (htraj : ∀ k, x (k + 1) = f (x k) (w k))
    (N : ℕ) (hd : ∀ k < N, γ (w k) ≤ d) :
    V (x N) ≤ ρ ^ N * V (x 0) + d / (1 - ρ) := by
  have hstep := iss_lyapunov_step_bound V f γ hρ0 hρ1 hdiss x w htraj N hd
  have hρ_pos : 0 < 1 - ρ := sub_pos.2 hρ1
  have hpow_nonneg : 0 ≤ ρ ^ N := pow_nonneg hρ0 N
  have hfrac : (1 - ρ ^ N) / (1 - ρ) ≤ 1 / (1 - ρ) :=
    div_le_div_of_nonneg_right (by linarith) hρ_pos.le
  have hmul : d * ((1 - ρ ^ N) / (1 - ρ)) ≤ d / (1 - ρ) := by
    calc d * ((1 - ρ ^ N) / (1 - ρ)) ≤ d * (1 / (1 - ρ)) :=
          mul_le_mul_of_nonneg_left hfrac hd0
      _ = d / (1 - ρ) := mul_one_div d (1 - ρ)
  linarith

/-! ### 2. Forward Invariance & Ultimate Boundedness of the ISS Sublevel Ball -/

/-- **One-Step Forward Invariance of the ISS Sublevel Ball**:
If $V(x) \le \frac{d}{1 - \rho}$ and $\gamma(w) \le d$, then $V(f(x, w)) \le \frac{d}{1 - \rho}$. -/
theorem iss_invariant_sublevel_step (V : X → ℝ) (f : X → W → X) (γ : W → ℝ) {ρ d : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiss : ∀ x w, V (f x w) ≤ ρ * V x + γ w)
    {x : X} {w : W} (hx : V x ≤ d / (1 - ρ)) (hw : γ w ≤ d) :
    V (f x w) ≤ d / (1 - ρ) := by
  have hρ_ne : 1 - ρ ≠ 0 := (sub_pos.2 hρ1).ne'
  calc V (f x w) ≤ ρ * V x + γ w := hdiss x w
    _ ≤ ρ * (d / (1 - ρ)) + d := add_le_add (mul_le_mul_of_nonneg_left hx hρ0) hw
    _ = d / (1 - ρ) := by
        field_simp [hρ_ne]
        ring

/-- **Trajectory Forward Invariance of the ISS Sublevel Ball**:
The sublevel set $\{x \mid V(x) \le \frac{d}{1 - \rho}\}$ is forward invariant for all $N \ge 0$
under any disturbance sequence satisfying $\gamma(w_k) \le d$. -/
theorem iss_invariant_sublevel (V : X → ℝ) (f : X → W → X) (γ : W → ℝ) {ρ d : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiss : ∀ x w, V (f x w) ≤ ρ * V x + γ w)
    (x : ℕ → X) (w : ℕ → W) (htraj : ∀ k, x (k + 1) = f (x k) (w k))
    (hx₀ : V (x 0) ≤ d / (1 - ρ)) (hd : ∀ k, γ (w k) ≤ d) :
    ∀ N : ℕ, V (x N) ≤ d / (1 - ρ)
  | 0 => hx₀
  | N + 1 => by
    rw [htraj N]
    exact iss_invariant_sublevel_step V f γ hρ0 hρ1 hdiss
      (iss_invariant_sublevel V f γ hρ0 hρ1 hdiss x w htraj hx₀ hd N) (hd N)

/-- **ISS Ultimate Boundedness Theorem**:
For every initial state $x_0$ and every $\varepsilon > 0$, there exists a finite horizon $K \in \mathbb{N}$
such that for all $N \ge K$,
$$V(x_N) \le \frac{d}{1 - \rho} + \varepsilon.$$ -/
theorem iss_ultimate_bound (V : X → ℝ) (f : X → W → X) (γ : W → ℝ) {ρ d : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiss : ∀ x w, V (f x w) ≤ ρ * V x + γ w)
    (x : ℕ → X) (w : ℕ → W) (htraj : ∀ k, x (k + 1) = f (x k) (w k))
    (hd : ∀ k, γ (w k) ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ N ≥ K, V (x N) ≤ d / (1 - ρ) + ε := by
  have hlim : Tendsto (fun N : ℕ => ρ ^ N * (V (x 0) - d / (1 - ρ))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (V (x 0) - d / (1 - ρ))
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε))
  refine ⟨K, fun N hN => ?_⟩
  have hstep := iss_lyapunov_step_bound V f γ hρ0 hρ1 hdiss x w htraj N (fun k _ => hd k)
  have hρ_ne : 1 - ρ ≠ 0 := (sub_pos.2 hρ1).ne'
  have h_id :
      ρ ^ N * V (x 0) + d * ((1 - ρ ^ N) / (1 - ρ)) =
        d / (1 - ρ) + ρ ^ N * (V (x 0) - d / (1 - ρ)) := by
    field_simp [hρ_ne]
    ring
  have hlt : ρ ^ N * (V (x 0) - d / (1 - ρ)) < ε := hK N hN
  linarith

/-! ### 3. Converging-Disturbance Asymptotic Stability -/

/-- **Scalar Converging-Input Converging-State Lemma**:
If $0 \le a_k$, $a_{k+1} \le \rho a_k + d_k$ with $0 \le \rho < 1$, and $d_k \to 0$,
then $a_k \to 0$ as $k \to \infty$. -/
theorem tendsto_zero_of_linear_dissipation {a d : ℕ → ℝ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (ha : ∀ k, 0 ≤ a k)
    (hstep : ∀ k, a (k + 1) ≤ ρ * a k + d k)
    (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hρ_pos : 0 < 1 - ρ := sub_pos.2 hρ1
  have hδ : 0 < ε / 2 * (1 - ρ) := mul_pos (half_pos hε) hρ_pos
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.1 hd (ε / 2 * (1 - ρ)) hδ
  have hd_bound : ∀ k ≥ K₀, d k ≤ ε / 2 * (1 - ρ) := fun k hk => by
    have h := hK₀ k hk
    rw [Real.dist_eq, sub_zero] at h
    exact (le_abs_self _).trans h.le
  have hiter : ∀ m : ℕ, a (K₀ + m) ≤ ρ ^ m * a K₀ + ε / 2 := by
    intro m
    induction m with
    | zero =>
      simp only [Nat.add_zero, pow_zero, one_mul, le_add_iff_nonneg_right]
      positivity
    | succ m ih =>
      have h1 := hstep (K₀ + m)
      have h2 := hd_bound (K₀ + m) (Nat.le_add_right K₀ m)
      rw [show K₀ + (m + 1) = K₀ + m + 1 by omega]
      calc a (K₀ + m + 1) ≤ ρ * a (K₀ + m) + d (K₀ + m) := h1
        _ ≤ ρ * (ρ ^ m * a K₀ + ε / 2) + ε / 2 * (1 - ρ) :=
            add_le_add (mul_le_mul_of_nonneg_left ih hρ0) h2
        _ = ρ ^ (m + 1) * a K₀ + ε / 2 := by
            rw [pow_succ']
            ring
  have hlim : Tendsto (fun m : ℕ => ρ ^ m * a K₀) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (a K₀)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨K₀ + M, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha n)]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show K₀ ≤ n by omega)
  have hm : M ≤ m := by omega
  have hpow : ρ ^ m * a K₀ < ε / 2 := hM m hm
  have h_le := hiter m
  linarith

/-- **Converging-Disturbance ISS Asymptotic Stability**:
If $0 \le V(x_k)$, $V(f(x, w)) \le \rho V(x) + \gamma(w)$ with $0 \le \rho < 1$, and
$\gamma(w_k) \to 0$ as $k \to \infty$, then $V(x_k) \to 0$ as $k \to \infty$. -/
theorem iss_tendsto_zero_of_disturbance_tendsto_zero (V : X → ℝ) (f : X → W → X) (γ : W → ℝ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hV_nonneg : ∀ x, 0 ≤ V x)
    (hdiss : ∀ x w, V (f x w) ≤ ρ * V x + γ w)
    (x : ℕ → X) (w : ℕ → W) (htraj : ∀ k, x (k + 1) = f (x k) (w k))
    (hγ : Tendsto (fun k => γ (w k)) atTop (𝓝 0)) :
    Tendsto (fun k => V (x k)) atTop (𝓝 0) := by
  refine tendsto_zero_of_linear_dissipation hρ0 hρ1 (fun k => hV_nonneg (x k)) (fun k => ?_) hγ
  rw [htraj k]
  exact hdiss (x k) (w k)

end ScalarISS

/-! ### 4. Matrix Peter–Paul Inequality & Quadratic ISS for Schur-Stable Linear Systems -/

section QuadraticISS

variable {n : Type*} [Fintype n]

/-- **Exact Matrix Peter–Paul (Young) Completion-of-Squares Identity**:
For any symmetric matrix $P$ ($P^\top = P$), any $\varepsilon \ne 0$, and any vectors $u, v : n \to \mathbb{R}$,
$$\operatorname{quad} P (u + v) + \varepsilon^{-1} \operatorname{quad} P (\varepsilon \cdot u - v)
  = (1 + \varepsilon) \operatorname{quad} P u + (1 + \varepsilon^{-1}) \operatorname{quad} P v.$$ -/
theorem quad_add_peter_paul_identity {P : Matrix n n ℝ} (hP : Pᵀ = P)
    {ε : ℝ} (hε : ε ≠ 0) (u v : n → ℝ) :
    quad P (u + v) + ε⁻¹ * quad P (ε • u - v) =
      (1 + ε) * quad P u + (1 + ε⁻¹) * quad P v := by
  have hsym : v ⬝ᵥ (P *ᵥ u) = u ⬝ᵥ (P *ᵥ v) := by
    rw [dotProduct_comm, mulVec_dotProduct_eq, hP]
  simp only [quad, mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, hsym]
  field_simp [hε]
  ring

/-- **Matrix Peter–Paul / Young Inequality**:
For any symmetric positive semidefinite matrix $P$ (`SymPSD P`) and any $\varepsilon > 0$,
$$\operatorname{quad} P (u + v) \le (1 + \varepsilon) \operatorname{quad} P u + (1 + \varepsilon^{-1}) \operatorname{quad} P v.$$ -/
theorem quad_add_le_peter_paul {P : Matrix n n ℝ} (hP : SymPSD P)
    {ε : ℝ} (hε : 0 < ε) (u v : n → ℝ) :
    quad P (u + v) ≤ (1 + ε) * quad P u + (1 + ε⁻¹) * quad P v := by
  have hid := quad_add_peter_paul_identity hP.1 hε.ne' u v
  have hnonneg : 0 ≤ ε⁻¹ * quad P (ε • u - v) :=
    mul_nonneg (inv_nonneg.2 hε.le) (hP.2 (ε • u - v))
  linarith

/-- **Quadratic ISS Step Bound from the Stein Equation**:
If $P$ is symmetric PSD (`SymPSD P`), $A^\top P A - P = -Q$, and $Q$ dominates $\alpha P$
($\forall x, \alpha \operatorname{quad} P x \le \operatorname{quad} Q x$) with $\alpha \le 1$,
then for every $\varepsilon > 0$ and every state $x$ and disturbance $w$:
$$\operatorname{quad} P (A x + w) \le
  (1 + \varepsilon)(1 - \alpha) \operatorname{quad} P x + (1 + \varepsilon^{-1}) \operatorname{quad} P w.$$ -/
theorem quad_iss_of_stein {A P Q : Matrix n n ℝ} (hP : SymPSD P)
    (hstein : Aᵀ * P * A - P = -Q) {α : ℝ} (_hα1 : α ≤ 1)
    (hQα : ∀ x, α * quad P x ≤ quad Q x) {ε : ℝ} (hε : 0 < ε) (x w : n → ℝ) :
    quad P (A *ᵥ x + w) ≤
      (1 + ε) * (1 - α) * quad P x + (1 + ε⁻¹) * quad P w := by
  have hpp := quad_add_le_peter_paul hP hε (A *ᵥ x) w
  have hAx_eq : quad P (A *ᵥ x) = quad P x - quad Q x := by
    have h := congr_arg (fun M => quad M x) hstein
    simp only [quad_sub, ← quad_mulVec, quad_neg] at h
    linarith
  have hAx_le : quad P (A *ᵥ x) ≤ (1 - α) * quad P x := by
    have := hQα x
    linarith
  have h1ε_pos : 0 ≤ 1 + ε := by linarith
  calc quad P (A *ᵥ x + w)
      ≤ (1 + ε) * quad P (A *ᵥ x) + (1 + ε⁻¹) * quad P w := hpp
    _ ≤ (1 + ε) * ((1 - α) * quad P x) + (1 + ε⁻¹) * quad P w :=
        add_le_add (mul_le_mul_of_nonneg_left hAx_le h1ε_pos) le_rfl
    _ = (1 + ε) * (1 - α) * quad P x + (1 + ε⁻¹) * quad P w := by ring

/-- **Explicit Choice of Peter–Paul Parameter $\varepsilon = \frac{\alpha}{2(1 - \alpha)}$**:
When $0 < \alpha < 1$, choosing $\varepsilon = \frac{\alpha}{2(1 - \alpha)}$ yields the strict contraction
rate $\rho = 1 - \frac{\alpha}{2} \in (0, 1)$ and disturbance weight $\frac{2 - \alpha}{\alpha} > 1$:
$$\operatorname{quad} P (A x + w) \le
  \left(1 - \frac{\alpha}{2}\right) \operatorname{quad} P x + \frac{2 - \alpha}{\alpha} \operatorname{quad} P w.$$ -/
theorem quad_iss_of_stein_explicit {A P Q : Matrix n n ℝ} (hP : SymPSD P)
    (hstein : Aᵀ * P * A - P = -Q) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hQα : ∀ x, α * quad P x ≤ quad Q x) (x w : n → ℝ) :
    quad P (A *ᵥ x + w) ≤
      (1 - α / 2) * quad P x + ((2 - α) / α) * quad P w := by
  have h1α : 0 < 1 - α := sub_pos.2 hα1
  set ε : ℝ := α / (2 * (1 - α))
  have hε : 0 < ε := div_pos hα0 (mul_pos zero_lt_two h1α)
  have hstep := quad_iss_of_stein hP hstein hα1.le hQα hε x w
  have h_rate : (1 + ε) * (1 - α) = 1 - α / 2 := by
    dsimp [ε]
    field_simp [h1α.ne']
    ring
  have h_dist : 1 + ε⁻¹ = (2 - α) / α := by
    dsimp [ε]
    field_simp [hα0.ne', h1α.ne']
    ring
  rwa [h_rate, h_dist] at hstep

/-- **Quadratic Input-to-State Stability for Schur-Stable Linear Systems (`schur_quadratic_iss`)**:
Every Schur-stable matrix $A$ ($A^k x \to 0$ for all $x$) admits a positive definite Lyapunov
matrix $P \succ 0$, a contraction rate $\rho \in [0, 1)$, and a disturbance gain $\gamma > 0$ such
that for all states $x$ and disturbances $w$,
$$\operatorname{quad} P (A x + w) \le \rho \operatorname{quad} P x + \gamma \|w\|^2.$$ -/
theorem schur_quadratic_iss [DecidableEq n] {A : Matrix n n ℝ}
    (hA : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0)) :
    ∃ (P : Matrix n n ℝ) (ρ γ : ℝ),
      P.PosDef ∧ 0 ≤ ρ ∧ ρ < 1 ∧ 0 < γ ∧
      ∀ x w : n → ℝ, quad P (A *ᵥ x + w) ≤ ρ * quad P x + γ * ‖w‖ ^ 2 := by
  have hI_pos_quad : ∀ x : n → ℝ, x ≠ 0 → 0 < quad (1 : Matrix n n ℝ) x := by
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.1 hx
    simp only [quad, one_mulVec, dotProduct]
    refine lt_of_lt_of_le (mul_self_pos.2 hi) ?_
    exact Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
  have hI_pos : (1 : Matrix n n ℝ).PosDef :=
    PosDef.of_quad_pos transpose_one hI_pos_quad
  have hI_psd : SymPSD (1 : Matrix n n ℝ) :=
    ⟨transpose_one, quad_nonneg_of_posDef hI_pos⟩
  obtain ⟨P, hP_psd, hstein, hdom⟩ := converse_lyapunov_of_schur hA hI_psd
  have hP_pos_quad : ∀ x ≠ 0, 0 < quad P x := fun x hx =>
    lt_of_lt_of_le (hI_pos_quad x hx) (hdom x)
  have hP_posDef : P.PosDef := PosDef.of_quad_pos hP_psd.1 hP_pos_quad
  have hQ_pos_quad : ∀ x ≠ 0, 0 < quad (P - Aᵀ * P * A) x := fun x hx => by
    have hsub : P - Aᵀ * P * A = 1 := by
      calc P - Aᵀ * P * A = -(Aᵀ * P * A - P) := by abel
        _ = -(-(1 : Matrix n n ℝ)) := by rw [hstein]
        _ = 1 := neg_neg 1
    rw [hsub]
    exact hI_pos_quad x hx
  obtain ⟨ρ₀, hρ₀0, hρ₀1, hρ₀_step⟩ := exists_lyapunov_contraction hP_pos_quad hQ_pos_quad
  obtain ⟨C, hC_pos, hCP⟩ := exists_quad_upper P
  have h1ρ₀_pos : 0 < 1 + ρ₀ := by linarith
  set ε : ℝ := (1 - ρ₀) / (1 + ρ₀)
  have hε_pos : 0 < ε := div_pos (sub_pos.2 hρ₀1) h1ρ₀_pos
  have hρ_eq : (1 + ε) * ρ₀ ≤ (1 + ρ₀) / 2 := by
    have h_ident : (1 + ε) * ρ₀ = 2 * ρ₀ / (1 + ρ₀) := by
      dsimp [ε]
      field_simp [h1ρ₀_pos.ne']
      ring
    rw [h_ident, div_le_div_iff₀ h1ρ₀_pos zero_lt_two]
    nlinarith [sq_nonneg (1 - ρ₀)]
  refine ⟨P, (1 + ρ₀) / 2, (1 + ε⁻¹) * C, hP_posDef, by linarith, by linarith,
    mul_pos (by positivity) hC_pos, fun x w => ?_⟩
  have hpp := quad_add_le_peter_paul hP_psd hε_pos (A *ᵥ x) w
  have h1ε_nonneg : 0 ≤ 1 + ε := by positivity
  have h1ε_inv_nonneg : 0 ≤ 1 + ε⁻¹ := by positivity
  calc quad P (A *ᵥ x + w)
      ≤ (1 + ε) * quad P (A *ᵥ x) + (1 + ε⁻¹) * quad P w := hpp
    _ ≤ (1 + ε) * (ρ₀ * quad P x) + (1 + ε⁻¹) * (C * ‖w‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left (hρ₀_step x) h1ε_nonneg)
          (mul_le_mul_of_nonneg_left (hCP w) h1ε_inv_nonneg)
    _ = ((1 + ε) * ρ₀) * quad P x + ((1 + ε⁻¹) * C) * ‖w‖ ^ 2 := by ring
    _ ≤ ((1 + ρ₀) / 2) * quad P x + ((1 + ε⁻¹) * C) * ‖w‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hρ_eq (hP_psd.2 x)) le_rfl

/-- **Finite-Horizon Quadratic ISS Trajectory Bound for Schur-Stable Linear Systems**:
Under the quadratic ISS certificate `(P, ρ, γ)` of `schur_quadratic_iss`, any trajectory
$x_{k+1} = A x_k + w_k$ with bounded disturbance $\|w_k\| \le \bar w$ satisfies
$$\operatorname{quad} P (x_N) \le \rho^N \operatorname{quad} P (x_0) + \frac{\gamma \bar w^2}{1 - \rho}.$$ -/
theorem schur_quadratic_iss_trajectory_bound {A P : Matrix n n ℝ} {ρ γ wbar : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hγ : 0 < γ)
    (hiss : ∀ x w : n → ℝ, quad P (A *ᵥ x + w) ≤ ρ * quad P x + γ * ‖w‖ ^ 2)
    (x w : ℕ → n → ℝ) (htraj : ∀ k, x (k + 1) = A *ᵥ x k + w k)
    (N : ℕ) (hw : ∀ k < N, ‖w k‖ ≤ wbar) :
    quad P (x N) ≤ ρ ^ N * quad P (x 0) + (γ * wbar ^ 2) / (1 - ρ) := by
  refine iss_lyapunov_uniform_bound (quad P) (fun s d => A *ᵥ s + d)
    (fun d => γ * ‖d‖ ^ 2) hρ0 hρ1 (by positivity) hiss x w htraj N (fun k hk => ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hw k hk) 2) hγ.le

end QuadraticISS

end ControlsLean.Controls
