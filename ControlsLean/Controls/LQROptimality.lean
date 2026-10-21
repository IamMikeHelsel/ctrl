/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.DAREUniqueness

/-!
# LQR Optimality: The DARE Solution Is the Minimal Cost

The previous files construct the DARE solution $P$ and show its gain is stabilizing. This file
proves that $P$ really *is* the optimal cost, against **all** open-loop input sequences.

For $x_{k+1} = A x_k + B u_k$ with stage cost $\ell(x, u) = x^\top Q x + u^\top R u$:

- `riccatiIter_le_lqrCost` (**finite horizon**): for every input sequence $u$ and horizon $N$,
  $x_0^\top P_N x_0 \le \sum_{k<N} \ell(x_k, u_k)$, where $P_N$ is the $N$-th Riccati iterate.
- `lqrCost_feedback_eq` (**telescoping**): under $u_k = -K x_k$ with $P = \mathcal{T}(P)$,
  $\sum_{k<N} \ell(x_k, u_k) = x_0^\top P x_0 - x_N^\top P x_N$.
- `lqr_infinite_horizon_optimal` (**infinite horizon**): under $R \succ 0$, $Q \succ 0$ and
  stabilizability, the unique PSD DARE solution $P$ and its gain $K$ satisfy:
  1. the feedback $u_k = -K x_k$ has total cost exactly $x_0^\top P x_0$;
  2. every input sequence with finite total cost has cost at least $x_0^\top P x_0$.
-/

namespace ControlsLean.Controls

open Matrix Filter Topology ControlsLean.Tactics

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
variable {A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ} {R : Matrix m m ℝ}

/-- State trajectory under an open-loop input sequence. -/
def lqrTraj (A : Matrix n n ℝ) (B : Matrix n m ℝ) (x₀ : n → ℝ) (u : ℕ → m → ℝ) : ℕ → n → ℝ
  | 0 => x₀
  | k + 1 => A *ᵥ lqrTraj A B x₀ u k + B *ᵥ u k

/-- Stage cost $\ell(x, u) = x^\top Q x + u^\top R u$. -/
def lqrStage (Q : Matrix n n ℝ) (R : Matrix m m ℝ) (x : n → ℝ) (u : m → ℝ) : ℝ :=
  quad Q x + quad R u

/-- Finite-horizon cost $J_N(x_0, u) = \sum_{k<N} \ell(x_k, u_k)$. -/
def lqrCost (A : Matrix n n ℝ) (B : Matrix n m ℝ) (Q : Matrix n n ℝ) (R : Matrix m m ℝ)
    (x₀ : n → ℝ) (u : ℕ → m → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, lqrStage Q R (lqrTraj A B x₀ u k) (u k)

omit [DecidableEq m] in
/-- Shifting the trajectory by one step. -/
theorem lqrTraj_succ_shift (x₀ : n → ℝ) (u : ℕ → m → ℝ) :
    ∀ k, lqrTraj A B x₀ u (k + 1) = lqrTraj A B (A *ᵥ x₀ + B *ᵥ u 0) (fun j => u (j + 1)) k
  | 0 => rfl
  | k + 1 => by
    change A *ᵥ lqrTraj A B x₀ u (k + 1) + B *ᵥ u (k + 1) = _
    rw [lqrTraj_succ_shift x₀ u k]
    rfl

omit [DecidableEq m] in
/-- Dynamic-programming split of the cost: first stage plus cost-to-go. -/
theorem lqrCost_succ (x₀ : n → ℝ) (u : ℕ → m → ℝ) (N : ℕ) :
    lqrCost A B Q R x₀ u (N + 1) =
      lqrStage Q R x₀ (u 0) + lqrCost A B Q R (A *ᵥ x₀ + B *ᵥ u 0) (fun j => u (j + 1)) N := by
  unfold lqrCost
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lqrTraj_succ_shift]

/-- **Finite-horizon optimality**: the $N$-th Riccati iterate lower-bounds the $N$-step cost of
*every* input sequence. -/
theorem riccatiIter_le_lqrCost (hR : R.PosDef) (hQ : SymPSD Q) :
    ∀ (N : ℕ) (x₀ : n → ℝ) (u : ℕ → m → ℝ),
      quad (riccatiIter A B Q R N) x₀ ≤ lqrCost A B Q R x₀ u N
  | 0, x₀, u => by simp [riccatiIter, lqrCost, quad]
  | N + 1, x₀, u => by
    have hP := riccatiIter_symPSD (A := A) (B := B) hR hQ N
    have hR' := hR
    rw [posDef_iff_quad_pos] at hR'
    have hbell := lqr_bellman_min_le (B := B) (Q := Q) hP.1 hR'.1
      (riccatiGain_normal_eq (A := A) (B := B) hR hP)
      (quad_nonneg_of_posDef (lqrHessian_posDef (B := B) hR hP)) x₀ (u 0)
    have ih := riccatiIter_le_lqrCost hR hQ N (A *ᵥ x₀ + B *ᵥ u 0) (fun j => u (j + 1))
    change quad (riccatiMap A B Q R (riccatiIter A B Q R N)) x₀ ≤ _
    rw [lqrCost_succ]
    unfold riccatiMap lqrStage
    linarith

omit [DecidableEq m] in
/-- Under linear feedback, the trajectory is $x_k = (A - BK)^k x_0$. -/
theorem lqrTraj_feedback [DecidableEq n] (K : Matrix m n ℝ) (x₀ : n → ℝ) :
    ∀ k, lqrTraj A B x₀ (fun j => -(K *ᵥ ((lqrClosedLoop A B K ^ j) *ᵥ x₀))) k =
      (lqrClosedLoop A B K ^ k) *ᵥ x₀
  | 0 => by simp [lqrTraj]
  | k + 1 => by
    change A *ᵥ lqrTraj A B x₀ _ k + B *ᵥ -(K *ᵥ ((lqrClosedLoop A B K ^ k) *ᵥ x₀)) = _
    rw [lqrTraj_feedback K x₀ k, pow_succ', ← mulVec_mulVec]
    simp only [lqrClosedLoop, mulVec_neg, mulVec_mulVec, sub_eq_add_neg, Matrix.add_mul,
      add_mulVec, Matrix.neg_mul, neg_mulVec, Matrix.mul_assoc]

omit [DecidableEq m] in
/-- **Telescoping cost under the DARE feedback**: if $P = \mathcal{R}_K(P)$, then under
$u_k = -K x_k$ the $N$-step cost is $x_0^\top P x_0 - x_N^\top P x_N$. -/
theorem lqrCost_feedback_eq [DecidableEq n] {P : Matrix n n ℝ} {K : Matrix m n ℝ}
    (hfix : lqrJosephUpdate P A B Q R K = P) (x₀ : n → ℝ) (N : ℕ) :
    lqrCost A B Q R x₀ (fun j => -(K *ᵥ ((lqrClosedLoop A B K ^ j) *ᵥ x₀))) N =
      quad P x₀ - quad P ((lqrClosedLoop A B K ^ N) *ᵥ x₀) := by
  have hstep : ∀ x : n → ℝ, lqrStage Q R x (-(K *ᵥ x)) =
      quad P x - quad P (lqrClosedLoop A B K *ᵥ x) := fun x => by
    have h := quad_lqrJosephUpdate P A B Q R K x
    rw [hfix] at h
    have hneg : quad R (-(K *ᵥ x)) = quad R (K *ᵥ x) := by
      simp [quad, mulVec_neg]
    unfold lqrStage
    rw [hneg]
    linarith
  unfold lqrCost
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, lqrTraj_feedback, hstep, mulVec_mulVec, ← pow_succ']
    ring

/-- **Infinite-horizon LQR optimality.** Let $R \succ 0$, $Q \succ 0$, and let $(A, B)$ be
stabilizable. Then there is a unique symmetric PSD DARE solution $P$, with gain $K = K(P)$, such
that for every initial state $x_0$:
1. the feedback $u_k = -K x_k$ has summable stage costs with total exactly $x_0^\top P x_0$;
2. every input sequence $u$ with summable stage costs has total cost $\ge x_0^\top P x_0$.

So $x_0^\top P x_0$ is the minimum infinite-horizon cost, and linear feedback attains it. -/
theorem lqr_infinite_horizon_optimal [DecidableEq n] (hR : R.PosDef) (hQ : Q.PosDef)
    (K₀ : Matrix m n ℝ)
    (hK₀ : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (lqrClosedLoop A B K₀ ^ k) *ᵥ x) atTop (𝓝 0)) :
    ∃ P : Matrix n n ℝ, (SymPSD P ∧ riccatiMap A B Q R P = P) ∧
      (∀ P', SymPSD P' ∧ riccatiMap A B Q R P' = P' → P' = P) ∧
      ∀ x₀ : n → ℝ,
        HasSum (fun k => lqrStage Q R
            (lqrTraj A B x₀ (fun j => -(riccatiGain A B R P *ᵥ
              ((lqrClosedLoop A B (riccatiGain A B R P) ^ j) *ᵥ x₀))) k)
            (-(riccatiGain A B R P *ᵥ ((lqrClosedLoop A B (riccatiGain A B R P) ^ k) *ᵥ x₀))))
          (quad P x₀) ∧
        ∀ u : ℕ → m → ℝ, Summable (fun k => lqrStage Q R (lqrTraj A B x₀ u k) (u k)) →
          quad P x₀ ≤ ∑' k, lqrStage Q R (lqrTraj A B x₀ u k) (u k) := by
  obtain ⟨P, ⟨hP, hfix⟩, huniq, -, hT, hstab⟩ := lqr_existsUnique_of_stabilizable hR hQ K₀ hK₀
  have hQ' := hQ
  rw [posDef_iff_quad_pos] at hQ'
  have hQpsd : SymPSD Q := ⟨hQ'.1, quad_nonneg_of_posDef hQ⟩
  have hstage0 : ∀ x v, 0 ≤ lqrStage Q R x v := fun x v =>
    add_nonneg (hQpsd.2 x) (quad_nonneg_of_posDef hR v)
  refine ⟨P, ⟨hP, hfix⟩, huniq, fun x₀ => ⟨?_, fun u hu => ?_⟩⟩
  · -- the optimal feedback attains `quad P x₀`
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => hstage0 _ _)]
    have hcost := lqrCost_feedback_eq (Q := Q) (R := R) (hfix : lqrJosephUpdate P A B Q R
      (riccatiGain A B R P) = P) x₀
    have hlim : Tendsto (fun N => quad P x₀ -
        quad P ((lqrClosedLoop A B (riccatiGain A B R P) ^ N) *ᵥ x₀)) atTop
        (𝓝 (quad P x₀ - quad P 0)) :=
      tendsto_const_nhds.sub (((continuous_quad P).tendsto 0).comp (hstab x₀))
    have hzero : quad P x₀ - quad P 0 = quad P x₀ := by simp [quad]
    rw [hzero] at hlim
    refine hlim.congr fun N => ?_
    exact (hcost N).symm
  · -- every finite-cost input does at least as badly
    have hle : ∀ N, quad (riccatiIter A B Q R N) x₀ ≤
        ∑' k, lqrStage Q R (lqrTraj A B x₀ u k) (u k) := fun N =>
      (riccatiIter_le_lqrCost hR hQpsd N x₀ u).trans
        (hu.sum_le_tsum (Finset.range N) fun k _ => hstage0 _ _)
    exact le_of_tendsto' (tendsto_quad_of_tendsto hT x₀) hle

end ControlsLean.Controls
