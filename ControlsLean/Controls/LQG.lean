/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Estimation.SteadyStateKalman

/-!
# LQG: Separation-Principle Stability of LQR + Steady-State Kalman Feedback

`Observer.lean` proves the *algebraic* separation principle: the closed-loop matrix is block
triangular and its characteristic polynomial factors. This file proves the *dynamical* statement
engineers rely on: the output-feedback loop is asymptotically stable when the LQR gain and the
steady-state Kalman gain from the existence theory are used.

## Converging-input, converging-state (`tendsto_zero_of_schur_forced`)

If $A$ is Schur stable and $x_{k+1} = A x_k + d_k$ with $d_k \to 0$, then $x_k \to 0$. The proof
uses the uniform contraction $\|A^N y\| \le \frac12\|y\|$ from `SchurLyapunov.lean` and an
$\varepsilon$-argument on the block recursion
$\|x_{k+N}\| \le \tfrac12 \|x_k\| + C \sum_{j<N} \|d_{k+j}\|$.

## LQG closed loop

Plant $x_{k+1} = A x_k + B u_k$, measurement $y_k = C x_k$, certainty-equivalence control
$u_k = -K \hat x_k$, and observer $\hat x_{k+1} = A \hat x_k + B u_k + L (y_k - C \hat x_k)$.

- `lqgTraj_error_step`: the error $e_k = x_k - \hat x_k$ obeys $e_{k+1} = (A - LC) e_k$.
- `lqgTraj_state_step`: $x_{k+1} = (A - BK) x_k + BK e_k$.
- `lqg_stable_of_stable_gains`: if $A - BK$ and $A - LC$ are Schur stable, then
  $x_k \to 0$ and $\hat x_k \to 0$ for all initial conditions.
- `lqg_closed_loop_stable`: under $Q, R, W, V \succ 0$, $(A,B)$ stabilizable and $(A,C)$
  detectable, the LQG controller built from the unique DARE / filtering-ARE solutions
  stabilizes the closed loop.
-/

namespace ControlsLean.Controls

open Matrix Filter Topology ControlsLean.Tactics ControlsLean.Estimation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### 1. Converging input, converging state -/

/-- Column-sum operator bound $\|M y\| \le (\sum_i \|M e_i\|)\, \|y\|$. -/
theorem norm_mulVec_le_colSum (M : Matrix n n ℝ) (y : n → ℝ) :
    ‖M *ᵥ y‖ ≤ (∑ i, ‖M *ᵥ Pi.single i 1‖) * ‖y‖ := by
  conv_lhs => rw [pi_eq_sum_univ' y]
  rw [mulVec_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [mulVec_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) (norm_nonneg _)

omit [Fintype n] [DecidableEq n] in
/-- A scalar sequence satisfying $a_{k+N} \le \tfrac12 a_k + b_k$, with $a \ge 0$ and $b_k \to 0$,
tends to zero. -/
theorem tendsto_zero_of_block_contraction {a b : ℕ → ℝ} {N : ℕ} (hN : 0 < N)
    (ha : ∀ k, 0 ≤ a k) (hrec : ∀ k, a (k + N) ≤ (1 / 2) * a k + b k)
    (hb : Tendsto b atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.1 hb (ε / 4) (by positivity)
  have hbK : ∀ k ≥ K₀, b k ≤ ε / 4 := fun k hk => by
    have := hK₀ k hk
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  -- iterate along blocks starting at any `k ≥ K₀`
  have hiter : ∀ q k, K₀ ≤ k → a (k + q * N) ≤ (1 / 2) ^ q * a k + ε / 2 := by
    intro q
    induction q with
    | zero =>
      intro k _
      simp only [zero_mul, add_zero, pow_zero, one_mul, le_add_iff_nonneg_right]
      positivity
    | succ q ih =>
      intro k hk
      have h1 := hrec (k + q * N)
      have h2 := hbK (k + q * N) (by omega)
      have h3 := ih k hk
      rw [show k + (q + 1) * N = k + q * N + N by ring]
      calc a (k + q * N + N) ≤ (1 / 2) * a (k + q * N) + b (k + q * N) := h1
        _ ≤ (1 / 2) * ((1 / 2) ^ q * a k + ε / 2) + ε / 4 := by gcongr
        _ = (1 / 2) ^ (q + 1) * a k + ε / 2 := by ring
  set M : ℝ := ∑ r ∈ Finset.range N, a (K₀ + r)
  have hM : ∀ r < N, a (K₀ + r) ≤ M := fun r hr =>
    Finset.single_le_sum (fun j _ => ha (K₀ + j)) (Finset.mem_range.2 hr)
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => ha (K₀ + j)
  obtain ⟨Q, hQ⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (2 * (M + 1)) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨K₀ + Q * N + N, fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha t)]
  -- write `t = K₀ + r + q * N` with `r < N` and `q ≥ Q`
  obtain ⟨q, r, hr, ht_eq⟩ : ∃ q r, r < N ∧ t = K₀ + r + q * N :=
    ⟨(t - K₀) / N, (t - K₀) % N, Nat.mod_lt _ hN, by
      have := Nat.mod_add_div (t - K₀) N
      rw [mul_comm] at this
      omega⟩
  have h1 : Q * N < (q + 1) * N := by
    rw [add_mul, one_mul]
    omega
  have hqQ : Q ≤ q := Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_right h1)
  have hbound := hiter q (K₀ + r) (by omega)
  rw [← ht_eq] at hbound
  have hpow : (1 / 2 : ℝ) ^ q ≤ (1 / 2) ^ Q := pow_le_pow_of_le_one (by norm_num) (by norm_num) hqQ
  have hprod : (1 / 2 : ℝ) ^ q * a (K₀ + r) < ε / 2 := by
    calc (1 / 2 : ℝ) ^ q * a (K₀ + r) ≤ (1 / 2) ^ Q * (M + 1) :=
          mul_le_mul hpow (by linarith [hM r hr]) (ha _) (by positivity)
      _ < ε / (2 * (M + 1)) * (M + 1) := by gcongr
      _ = ε / 2 := by field_simp
  linarith

/-- Block expansion of a forced linear recursion:
$x_{k+i} = A^i x_k + \sum_{j<i} A^{i-1-j} d_{k+j}$. -/
theorem forced_block_expansion {A : Matrix n n ℝ} {x d : ℕ → n → ℝ}
    (hx : ∀ k, x (k + 1) = A *ᵥ x k + d k) (k : ℕ) :
    ∀ i, x (k + i) = (A ^ i) *ᵥ x k + ∑ j ∈ Finset.range i, (A ^ (i - 1 - j)) *ᵥ d (k + j)
  | 0 => by simp
  | i + 1 => by
    rw [← add_assoc, hx, forced_block_expansion hx k i, mulVec_add, mulVec_mulVec, ← pow_succ',
      Finset.sum_range_succ, mulVec_sum, Finset.sum_congr rfl fun j hj => ?_]
    · simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mulVec]
      abel
    · rw [mulVec_mulVec, ← pow_succ']
      congr 2
      have := Finset.mem_range.1 hj
      omega

/-- **Converging-input converging-state.** If $A$ is Schur stable, $x_{k+1} = A x_k + d_k$ and
$d_k \to 0$, then $x_k \to 0$. -/
theorem tendsto_zero_of_schur_forced {A : Matrix n n ℝ}
    (hA : ∀ y : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ y) atTop (𝓝 0))
    {x d : ℕ → n → ℝ} (hx : ∀ k, x (k + 1) = A *ᵥ x k + d k)
    (hd : Tendsto d atTop (𝓝 0)) : Tendsto x atTop (𝓝 0) := by
  obtain ⟨N, hNpos, hN⟩ := exists_pow_contraction hA
  set C : ℝ := ∑ r ∈ Finset.range N, ∑ i, ‖(A ^ r) *ᵥ Pi.single i 1‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcol : ∀ r < N, ∑ i, ‖(A ^ r) *ᵥ Pi.single (M := fun _ => ℝ) i 1‖ ≤ C := fun r hr =>
    Finset.single_le_sum (f := fun r => ∑ i, ‖(A ^ r) *ᵥ Pi.single (M := fun _ => ℝ) i 1‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_range.2 hr)
  set b : ℕ → ℝ := fun k => C * ∑ j ∈ Finset.range N, ‖d (k + j)‖
  have hrec : ∀ k, ‖x (k + N)‖ ≤ (1 / 2) * ‖x k‖ + b k := by
    intro k
    rw [forced_block_expansion hx k N]
    refine (norm_add_le _ _).trans (add_le_add (hN _) ?_)
    refine (norm_sum_le _ _).trans ?_
    change _ ≤ C * _
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    refine (norm_mulVec_le_colSum _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hcol _ (by omega)) (norm_nonneg _)
  have hb : Tendsto b atTop (𝓝 0) := by
    have h : Tendsto (fun k => ∑ j ∈ Finset.range N, ‖d (k + j)‖) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.range N) fun j _ =>
        ((tendsto_add_atTop_iff_nat j).2 hd).norm
      simpa only [norm_zero, Finset.sum_const_zero] using this
    simpa using h.const_mul C
  have ha := tendsto_zero_of_block_contraction hNpos (fun k => norm_nonneg (x k)) hrec hb
  exact tendsto_zero_iff_norm_tendsto_zero.2 ha

/-! ### 2. The LQG closed loop -/

variable {m p : Type*} [Fintype m] [Fintype p]

/-- LQG closed-loop trajectory $(x_k, \hat x_k)$ under $u_k = -K \hat x_k$ and the observer
$\hat x_{k+1} = A \hat x_k + B u_k + L (C x_k - C \hat x_k)$. -/
def lqgTraj (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix p n ℝ) (K : Matrix m n ℝ)
    (L : Matrix n p ℝ) (x₀ xh₀ : n → ℝ) : ℕ → (n → ℝ) × (n → ℝ)
  | 0 => (x₀, xh₀)
  | k + 1 =>
    let s := lqgTraj A B C K L x₀ xh₀ k
    (A *ᵥ s.1 + B *ᵥ (-(K *ᵥ s.2)),
      A *ᵥ s.2 + B *ᵥ (-(K *ᵥ s.2)) + L *ᵥ (C *ᵥ s.1 - C *ᵥ s.2))

omit [DecidableEq n] in
/-- Error dynamics of the LQG loop: $e_{k+1} = (A - LC) e_k$. -/
theorem lqgTraj_error_step (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix p n ℝ)
    (K : Matrix m n ℝ) (L : Matrix n p ℝ) (x₀ xh₀ : n → ℝ) (k : ℕ) :
    (lqgTraj A B C K L x₀ xh₀ (k + 1)).1 - (lqgTraj A B C K L x₀ xh₀ (k + 1)).2 =
      (A - L * C) *ᵥ ((lqgTraj A B C K L x₀ xh₀ k).1 - (lqgTraj A B C K L x₀ xh₀ k).2) := by
  simp only [lqgTraj, sub_mulVec, mulVec_sub, ← mulVec_mulVec]
  abel

omit [DecidableEq n] in
/-- State dynamics of the LQG loop: $x_{k+1} = (A - BK) x_k + BK e_k$. -/
theorem lqgTraj_state_step (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix p n ℝ)
    (K : Matrix m n ℝ) (L : Matrix n p ℝ) (x₀ xh₀ : n → ℝ) (k : ℕ) :
    (lqgTraj A B C K L x₀ xh₀ (k + 1)).1 =
      lqrClosedLoop A B K *ᵥ (lqgTraj A B C K L x₀ xh₀ k).1 +
        (B * K) *ᵥ ((lqgTraj A B C K L x₀ xh₀ k).1 - (lqgTraj A B C K L x₀ xh₀ k).2) := by
  simp only [lqgTraj, lqrClosedLoop, sub_mulVec, mulVec_sub, mulVec_neg, ← mulVec_mulVec]
  abel

/-- **Separation-principle stability.** If $A - BK$ and $A - LC$ are both Schur stable, then the
LQG closed loop drives both the plant state and the estimate to zero. -/
theorem lqg_stable_of_stable_gains {A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ}
    {K : Matrix m n ℝ} {L : Matrix n p ℝ}
    (hK : ∀ y : n → ℝ, Tendsto (fun k : ℕ => (lqrClosedLoop A B K ^ k) *ᵥ y) atTop (𝓝 0))
    (hL : ∀ y : n → ℝ, Tendsto (fun k : ℕ => ((A - L * C) ^ k) *ᵥ y) atTop (𝓝 0))
    (x₀ xh₀ : n → ℝ) :
    Tendsto (fun k => (lqgTraj A B C K L x₀ xh₀ k).1) atTop (𝓝 0) ∧
      Tendsto (fun k => (lqgTraj A B C K L x₀ xh₀ k).2) atTop (𝓝 0) := by
  set e : ℕ → n → ℝ := fun k => (lqgTraj A B C K L x₀ xh₀ k).1 - (lqgTraj A B C K L x₀ xh₀ k).2
  have he_pow : ∀ k, e k = ((A - L * C) ^ k) *ᵥ e 0 := fun k =>
    linear_dynamics_pow (A - L * C) e (lqgTraj_error_step A B C K L x₀ xh₀) k
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

variable [DecidableEq m] [DecidableEq p]

/-- **LQG closed-loop stability.** Let $Q, R, W, V \succ 0$, let $(A, B)$ be stabilizable and let
$(A, C)$ be detectable. Take the unique PSD solutions $P$ of the control DARE and $\Sigma$ of the
filtering ARE, with LQR gain $K = K(P)$ and steady-state Kalman gain $L = L(\Sigma)$. Then the
output-feedback loop $u_k = -K \hat x_k$ with Kalman predictor $\hat x$ drives both $x_k$ and
$\hat x_k$ to zero from every initial condition. -/
theorem lqg_closed_loop_stable {A : Matrix n n ℝ} {B : Matrix n m ℝ} {C : Matrix p n ℝ}
    {Q W : Matrix n n ℝ} {R : Matrix m m ℝ} {V : Matrix p p ℝ}
    (hQ : Q.PosDef) (hR : R.PosDef) (hW : W.PosDef) (hV : V.PosDef)
    (K₀ : Matrix m n ℝ)
    (hK₀ : ∀ y : n → ℝ, Tendsto (fun k : ℕ => (lqrClosedLoop A B K₀ ^ k) *ᵥ y) atTop (𝓝 0))
    (L₀ : Matrix n p ℝ)
    (hL₀ : ∀ y : n → ℝ, Tendsto (fun k : ℕ => ((A - L₀ * C) ^ k) *ᵥ y) atTop (𝓝 0)) :
    ∃ P Sig : Matrix n n ℝ, riccatiMap A B Q R P = P ∧ kalmanMap A C W V Sig = Sig ∧
      P.PosDef ∧ Sig.PosDef ∧
      ∀ x₀ xh₀ : n → ℝ,
        Tendsto (fun k => (lqgTraj A B C (riccatiGain A B R P) (kalmanGain A C V Sig)
          x₀ xh₀ k).1) atTop (𝓝 0) ∧
        Tendsto (fun k => (lqgTraj A B C (riccatiGain A B R P) (kalmanGain A C V Sig)
          x₀ xh₀ k).2) atTop (𝓝 0) := by
  obtain ⟨P, ⟨-, hPfix⟩, -, hPpd, -, hPstab⟩ := lqr_existsUnique_of_stabilizable hR hQ K₀ hK₀
  obtain ⟨Sig, ⟨-, hSfix⟩, -, hSpd, -, -, hSstab⟩ := kalman_steady_state hV hW L₀ hL₀
  exact ⟨P, Sig, hPfix, hSfix, hPpd, hSpd, fun x₀ xh₀ =>
    lqg_stable_of_stable_gains hPstab hSstab x₀ xh₀⟩

end ControlsLean.Controls
