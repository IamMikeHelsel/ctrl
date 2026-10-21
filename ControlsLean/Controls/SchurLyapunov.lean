/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.DAREExistence

/-!
# Schur Stability Implies Solvability of the Stein Equation, and LQR from Stabilizability

`ConverseLyapunov.lean` proves the converse Lyapunov theorem *conditionally*: if the Lyapunov sums
$P_N = \sum_{k<N} (A^k)^\top Q A^k$ converge and the tail terms vanish, the limit solves the Stein
equation. This file discharges those hypotheses from plain **Schur stability**
($A^k x \to 0$ for every $x$), and then closes the loop with `DAREExistence.lean`:

- `exists_pow_contraction`: pointwise convergence $A^k x \to 0$ upgrades to a uniform contraction
  $\|A^N x\| \le \tfrac12 \|x\|$ for some $N \ge 1$.
- `norm_pow_mulVec_le`: geometric decay $\|A^{qN + r} x\| \le 2^{-q} \|A^r x\|$.
- `summable_quad_pow_mulVec`: $\sum_k x^\top (A^k)^\top Q A^k x$ converges for PSD $Q$.
- `lyapunovSum_tendsto_of_schur`, `lyapunov_tail_tendsto_zero_of_schur`: the hypotheses of the
  conditional converse Lyapunov theorem hold.
- `converse_lyapunov_of_schur`: Schur stability gives a symmetric PSD $S$ with
  $A^\top S A - S = -Q$ (and $S \succ 0$ if $Q \succ 0$).
- `lqr_exists_of_stabilizable`: **if some gain $K_0$ makes $A - BK_0$ Schur stable, $Q \succ 0$
  and $R \succ 0$, then Riccati value iteration converges to a positive definite DARE solution
  whose optimal gain is stabilizing.**
-/

namespace ControlsLean.Controls

open Matrix Filter Topology ControlsLean.Tactics

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### 1. From pointwise to uniform contraction -/

/-- If $A^k x \to 0$ for every $x$, then $\|A^N x\| \le \tfrac12 \|x\|$ for some $N \ge 1$. -/
theorem exists_pow_contraction {A : Matrix n n ℝ}
    (hA : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : n → ℝ, ‖(A ^ N) *ᵥ x‖ ≤ (1 / 2) * ‖x‖ := by
  set c : ℕ → ℝ := fun k => ∑ i, ‖(A ^ k) *ᵥ Pi.single i 1‖ with hc_def
  have hc : Tendsto c atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset n)
      (fun i _ => (hA (Pi.single i 1)).norm)
    simpa only [norm_zero, Finset.sum_const_zero] using h
  have hbound : ∀ k (x : n → ℝ), ‖(A ^ k) *ᵥ x‖ ≤ c k * ‖x‖ := by
    intro k x
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [mulVec_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [mulVec_smul, norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _)
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.1 (hc.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨N₀ + 1, Nat.succ_pos _, fun x => ?_⟩
  exact (hbound _ x).trans (mul_le_mul_of_nonneg_right (hN₀ _ (by omega)).le (norm_nonneg _))

/-- Geometric decay along blocks: $\|A^{qN + r} x\| \le 2^{-q} \|A^r x\|$. -/
theorem norm_pow_mulVec_le {A : Matrix n n ℝ} {N : ℕ}
    (hN : ∀ x : n → ℝ, ‖(A ^ N) *ᵥ x‖ ≤ (1 / 2) * ‖x‖) (x : n → ℝ) (r : ℕ) :
    ∀ q : ℕ, ‖(A ^ (q * N + r)) *ᵥ x‖ ≤ (1 / 2) ^ q * ‖(A ^ r) *ᵥ x‖
  | 0 => by simp
  | q + 1 => by
    have h : A ^ ((q + 1) * N + r) = A ^ N * A ^ (q * N + r) := by
      rw [← pow_add]
      congr 1
      ring
    rw [h, ← mulVec_mulVec, pow_succ]
    calc ‖(A ^ N) *ᵥ ((A ^ (q * N + r)) *ᵥ x)‖
        ≤ (1 / 2) * ‖(A ^ (q * N + r)) *ᵥ x‖ := hN _
      _ ≤ (1 / 2) * ((1 / 2) ^ q * ‖(A ^ r) *ᵥ x‖) :=
          mul_le_mul_of_nonneg_left (norm_pow_mulVec_le hN x r q) (by norm_num)
      _ = (1 / 2) ^ q * (1 / 2) * ‖(A ^ r) *ᵥ x‖ := by ring

/-! ### 2. Summability of the Lyapunov series -/

/-- For Schur-stable $A$ and PSD $Q$, the series $\sum_k (A^k x)^\top Q (A^k x)$ converges. -/
theorem summable_quad_pow_mulVec {A Q : Matrix n n ℝ}
    (hA : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0))
    (hQ : ∀ v, 0 ≤ quad Q v) (x : n → ℝ) :
    Summable fun k => quad Q ((A ^ k) *ᵥ x) := by
  obtain ⟨N, hNpos, hN⟩ := exists_pow_contraction hA
  obtain ⟨C, hC, hCQ⟩ := exists_quad_upper Q
  set g : ℕ → ℝ := fun k => quad Q ((A ^ k) *ᵥ x)
  set M : ℝ := ∑ r ∈ Finset.range N, ‖(A ^ r) *ᵥ x‖ ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg0 : ∀ k, 0 ≤ g k := fun k => hQ _
  -- one block of length `N` starting at `q * N`
  have hblock : ∀ q, ∑ r ∈ Finset.range N, g (q * N + r) ≤ C * M * (1 / 4) ^ q := by
    intro q
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun r _ => ?_
    have h1 := norm_pow_mulVec_le hN x r q
    have h2 : ‖(A ^ (q * N + r)) *ᵥ x‖ ^ 2 ≤ ((1 / 2) ^ q * ‖(A ^ r) *ᵥ x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc g (q * N + r) ≤ C * ‖(A ^ (q * N + r)) *ᵥ x‖ ^ 2 := hCQ _
      _ ≤ C * ((1 / 2) ^ q * ‖(A ^ r) *ᵥ x‖) ^ 2 := mul_le_mul_of_nonneg_left h2 hC.le
      _ = C * ‖(A ^ r) *ᵥ x‖ ^ 2 * (1 / 4) ^ q := by
          rw [mul_pow, ← pow_mul, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul]
          ring
  have hblocks : ∀ q, ∑ k ∈ Finset.range (q * N), g k ≤ C * M * (4 / 3) := by
    have hgeom : ∀ q, ∑ k ∈ Finset.range (q * N), g k ≤
        C * M * ∑ j ∈ Finset.range q, (1 / 4 : ℝ) ^ j := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [show (q + 1) * N = q * N + N by ring, Finset.sum_range_add, Finset.sum_range_succ,
          mul_add]
        exact add_le_add ih (hblock q)
    intro q
    refine (hgeom q).trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC.le hM))
    have h := geom_sum_eq (show (1 / 4 : ℝ) ≠ 1 by norm_num) q
    rw [h]
    have hp : 0 ≤ (1 / 4 : ℝ) ^ q := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    nlinarith
  refine summable_of_sum_range_le hg0 (c := C * M * (4 / 3)) fun k => ?_
  refine le_trans ?_ (hblocks k)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hg0 i
  exact Finset.range_subset_range.2 (Nat.le_mul_of_pos_right k hNpos)

/-! ### 3. Converse Lyapunov from Schur stability -/

/-- For Schur-stable $A$ and symmetric PSD $Q$, the Lyapunov sums converge. -/
theorem lyapunovSum_tendsto_of_schur {A Q : Matrix n n ℝ}
    (hA : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0))
    (hQ : SymPSD Q) :
    ∃ S : Matrix n n ℝ, Tendsto (lyapunovSum A Q) atTop (𝓝 S) := by
  refine ⟨polarMatrix fun x => ∑' k, quad Q ((A ^ k) *ᵥ x), ?_⟩
  refine tendsto_polarMatrix (fun N => lyapunovSum_transpose A Q hQ.1 N) fun x => ?_
  have h := (summable_quad_pow_mulVec hA hQ.2 x).hasSum.tendsto_sum_nat
  refine h.congr fun N => ?_
  rw [quad_lyapunovSum]

/-- For Schur-stable $A$, the Lyapunov tail terms $(A^N)^\top Q A^N$ vanish. -/
theorem lyapunov_tail_tendsto_zero_of_schur {A Q : Matrix n n ℝ}
    (hA : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0))
    (hQ : Qᵀ = Q) :
    Tendsto (fun N => (A ^ N)ᵀ * Q * (A ^ N)) atTop (𝓝 0) := by
  have h := tendsto_polarMatrix (q := fun _ => 0)
    (fun N => lyapunovTerm_transpose A Q hQ N) fun x => by
      have h0 := ((continuous_quad Q).tendsto 0).comp (hA x)
      simp only [quad, mulVec_zero, dotProduct_zero] at h0
      refine h0.congr fun N => ?_
      simp only [Function.comp_apply]
      exact (quad_lyapunovTerm A Q N x).symm
  have hzero : polarMatrix (n := n) (fun _ => 0) = 0 := by
    ext i j
    simp [polarMatrix]
  rwa [hzero] at h

/-- **Converse discrete Lyapunov theorem from Schur stability.** If $A^k x \to 0$ for every $x$
and $Q$ is symmetric PSD, then there is a symmetric PSD $S \succeq Q$ with $A^\top S A - S = -Q$. -/
theorem converse_lyapunov_of_schur {A Q : Matrix n n ℝ}
    (hA : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0))
    (hQ : SymPSD Q) :
    ∃ S : Matrix n n ℝ, SymPSD S ∧ Aᵀ * S * A - S = -Q ∧ LoewnerLE Q S := by
  obtain ⟨S, hS⟩ := lyapunovSum_tendsto_of_schur hA hQ
  obtain ⟨hstein, hsym, hdom⟩ := converse_lyapunov_of_tendsto_semidef A Q S hS
    (lyapunov_tail_tendsto_zero_of_schur hA hQ.1) hQ.1 hQ.2
  exact ⟨S, ⟨hsym, fun x => (hQ.2 x).trans (hdom x)⟩, hstein, hdom⟩

/-! ### 4. LQR from stabilizability -/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Discrete-time LQR existence theorem.** Let $R \succ 0$ and $Q \succ 0$. If the pair $(A, B)$
is stabilizable, i.e. some gain $K_0$ makes $(A - BK_0)^k x \to 0$ for every $x$, then Riccati
value iteration $P_0 = 0$, $P_{k+1} = \mathcal{T}(P_k)$ converges to a positive definite solution
$P$ of the DARE, $P = \mathcal{T}(P)$, and the optimal feedback $u = -K(P) x$ is stabilizing. -/
theorem lqr_exists_of_stabilizable {A Q : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ}
    (hR : R.PosDef) (hQ : Q.PosDef) (K₀ : Matrix m n ℝ)
    (hK₀ : ∀ x : n → ℝ, Tendsto (fun k : ℕ => (lqrClosedLoop A B K₀ ^ k) *ᵥ x) atTop (𝓝 0)) :
    ∃ P : Matrix n n ℝ, P.PosDef ∧ riccatiMap A B Q R P = P ∧
      Tendsto (riccatiIter A B Q R) atTop (𝓝 P) ∧
      ∀ x₀ : n → ℝ, Tendsto (fun k : ℕ => (lqrClosedLoop A B (riccatiGain A B R P) ^ k) *ᵥ x₀)
        atTop (𝓝 0) := by
  have hQ' := hQ
  rw [posDef_iff_quad_pos] at hQ'
  have hR' := hR
  rw [posDef_iff_quad_pos] at hR'
  have hQpsd : SymPSD Q := ⟨hQ'.1, quad_nonneg_of_posDef hQ⟩
  -- closed-loop stage cost is symmetric PSD
  have hQk : SymPSD (Q + K₀ᵀ * R * K₀) := by
    refine ⟨?_, fun v => ?_⟩
    · simp only [transpose_add, transpose_mul, transpose_transpose, hQ'.1, hR'.1,
        Matrix.mul_assoc]
    · rw [quad_add, ← quad_mulVec_rect]
      exact add_nonneg (hQpsd.2 v) (quad_nonneg_of_posDef hR _)
  obtain ⟨S, hS⟩ := lyapunovSum_tendsto_of_schur hK₀ hQk
  obtain ⟨hSpsd, hSeq⟩ := certificate_of_converse_lyapunov hR hQpsd K₀ hS
    (lyapunov_tail_tendsto_zero_of_schur hK₀ hQk.1)
  have hcert : LoewnerLE (lqrJosephUpdate S A B Q R K₀) S := by
    rw [hSeq]
    exact LoewnerLE.refl S
  obtain ⟨P, hT, hfix, hP, -⟩ := dare_exists_of_certificate hR hQpsd K₀ hSpsd hcert
  have hPpos : ∀ x ≠ 0, 0 < quad P x := fun x hx => by
    have h := quad_le_riccatiMap (A := A) (B := B) (Q := Q) hR hP x
    rw [hfix] at h
    exact (hQ'.2 x hx).trans_le h
  refine ⟨P, (posDef_iff_quad_pos P).2 ⟨hP.1, hPpos⟩, hfix, hT, fun x₀ => ?_⟩
  refine dare_closedLoop_tendsto_zero hPpos hfix (fun x hx => ?_) x₀
  rw [quad_add, ← quad_mulVec_rect]
  exact add_pos_of_pos_of_nonneg (hQ'.2 x hx) (quad_nonneg_of_posDef hR _)

end ControlsLean.Controls
