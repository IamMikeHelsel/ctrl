/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.PosDef
import ControlsLean.Controls.DiscreteLyapunov
import ControlsLean.Tactics.ControlTactics

/-!
# Converse Discrete-Time Lyapunov Theorem and Stein Telescoping Identities

This module formalizes the constructive core of the **Converse Discrete-Time Lyapunov Theorem**
for linear time-invariant (LTI) systems `x_{k+1} = A x_k`:

1. **Finite-Horizon Lyapunov Sum**:
   $$P_N = \sum_{k=0}^{N-1} (A^k)^\top Q A^k = \sum_{k=0}^{N-1} (A^\top)^k Q A^k.$$

2. **Exact Telescoping Discrete Stein / Lyapunov Identity**:
   $$A^\top P_N A - P_N = (A^N)^\top Q A^N - Q$$
   and at the quadratic form level:
   $$x^\top (A^\top P_N A - P_N) x = (A^N x)^\top Q (A^N x) - x^\top Q x.$$

3. **Symmetry & Positive-Definiteness Preservation**:
   - `lyapunovSum_transpose`: If $Q^\top = Q$, then $P_N^\top = P_N$.
   - `quad_lyapunovSum_ge`: For $N \ge 1$ and positive semidefinite $Q$, $x^\top P_N x \ge x^\top Q x$.
   - `posDef_lyapunovSum`: If $Q \succ 0$ and $N \ge 1$, then $P_N \succ 0$.

4. **Nilpotent / Deadbeat Exact Converse Lyapunov Certificate**:
   - `converse_lyapunov_nilpotent`: If $A^N = 0$ and $Q \succ 0$, then $P_N \succ 0$ and
     $A^\top P_N A - P_N = -Q$.

5. **Infinite-Horizon Limit Converse Lyapunov Certificate**:
   - `converse_lyapunov_of_tendsto`: If $P_N \to P$ and $(A^N)^\top Q A^N \to 0$ as $N \to \infty$,
     then $P$ satisfies $A^\top P A - P = -Q$, preserves $x^\top P x \ge x^\top Q x$ for
     positive semidefinite $Q$, and satisfies $P \succ 0$ whenever $Q \succ 0$.
-/

open Matrix Filter Topology BigOperators

namespace ControlsLean.Controls

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### 1. Finite-Horizon Lyapunov Sum and Matrix Power Transpose -/

/-- Matrix transposition commutes with natural number powers: `(A ^ k)ᵀ = (Aᵀ) ^ k`. -/
@[simp]
theorem transpose_pow (A : Matrix n n ℝ) (k : ℕ) : (A ^ k)ᵀ = (Aᵀ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ', transpose_mul, ih]

/-- The `k`-th stage Lyapunov summand `(A ^ k)ᵀ * Q * (A ^ k)`. -/
def lyapunovTerm (A Q : Matrix n n ℝ) (k : ℕ) : Matrix n n ℝ :=
  (A ^ k)ᵀ * Q * (A ^ k)

/-- The finite-horizon discrete Lyapunov sum:
`P_N = ∑ k ∈ Finset.range N, (A ^ k)ᵀ * Q * (A ^ k)`. -/
def lyapunovSum (A Q : Matrix n n ℝ) (N : ℕ) : Matrix n n ℝ :=
  ∑ k ∈ Finset.range N, (A ^ k)ᵀ * Q * (A ^ k)

/-- Equivalence of `lyapunovTerm` with `(Aᵀ ^ k) * Q * (A ^ k)`. -/
theorem lyapunovTerm_eq_transpose_pow (A Q : Matrix n n ℝ) (k : ℕ) :
    lyapunovTerm A Q k = (Aᵀ ^ k) * Q * (A ^ k) := by
  simp [lyapunovTerm]

/-- Equivalence of `lyapunovSum` with `∑ k ∈ Finset.range N, lyapunovTerm A Q k`. -/
theorem lyapunovSum_eq_sum_term (A Q : Matrix n n ℝ) (N : ℕ) :
    lyapunovSum A Q N = ∑ k ∈ Finset.range N, lyapunovTerm A Q k := rfl

/-- Equivalence of `lyapunovSum` with `(Aᵀ) ^ k` form:
`lyapunovSum A Q N = ∑ k ∈ Finset.range N, (Aᵀ ^ k) * Q * (A ^ k)`. -/
theorem lyapunovSum_eq_sum_transpose_pow (A Q : Matrix n n ℝ) (N : ℕ) :
    lyapunovSum A Q N = ∑ k ∈ Finset.range N, (Aᵀ ^ k) * Q * (A ^ k) := by
  unfold lyapunovSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [transpose_pow]

/-- Base case: the 0-horizon Lyapunov sum is zero. -/
@[simp]
theorem lyapunovSum_zero (A Q : Matrix n n ℝ) : lyapunovSum A Q 0 = 0 := by
  simp [lyapunovSum]

/-- Single-step horizon: `lyapunovSum A Q 1 = Q`. -/
@[simp]
theorem lyapunovSum_one (A Q : Matrix n n ℝ) : lyapunovSum A Q 1 = Q := by
  simp [lyapunovSum]

/-- Standard upper-index recurrence:
`P_{N+1} = P_N + (A ^ N)ᵀ * Q * (A ^ N)`. -/
theorem lyapunovSum_succ (A Q : Matrix n n ℝ) (N : ℕ) :
    lyapunovSum A Q (N + 1) = lyapunovSum A Q N + (A ^ N)ᵀ * Q * (A ^ N) := by
  unfold lyapunovSum
  rw [Finset.sum_range_succ]

/-- Congruence-shifted recurrence:
`P_{N+1} = Aᵀ * P_N * A + Q`. -/
theorem lyapunovSum_succ' (A Q : Matrix n n ℝ) (N : ℕ) :
    lyapunovSum A Q (N + 1) = Aᵀ * lyapunovSum A Q N * A + Q := by
  unfold lyapunovSum
  rw [Finset.sum_range_succ']
  simp only [pow_zero, transpose_one, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ, transpose_mul]
  simp only [Matrix.mul_assoc]

/-! ### 2. Exact Telescoping Discrete Stein / Lyapunov Identities -/

/-- **Exact Telescoping Discrete Stein / Lyapunov Identity**:
`Aᵀ * P_N * A - P_N = (A ^ N)ᵀ * Q * (A ^ N) - Q`. -/
theorem stein_telescoping (A Q : Matrix n n ℝ) (N : ℕ) :
    Aᵀ * lyapunovSum A Q N * A - lyapunovSum A Q N = (A ^ N)ᵀ * Q * (A ^ N) - Q := by
  have h1 := lyapunovSum_succ A Q N
  have h2 := lyapunovSum_succ' A Q N
  -- From h1 and h2: Aᵀ * P_N * A + Q = P_N + (A^N)ᵀ * Q * (A^N)
  have h_eq : Aᵀ * lyapunovSum A Q N * A + Q = lyapunovSum A Q N + (A ^ N)ᵀ * Q * (A ^ N) := by
    rw [← h2, h1]
  calc Aᵀ * lyapunovSum A Q N * A - lyapunovSum A Q N
      = (Aᵀ * lyapunovSum A Q N * A + Q) - lyapunovSum A Q N - Q := by abel
    _ = (lyapunovSum A Q N + (A ^ N)ᵀ * Q * (A ^ N)) - lyapunovSum A Q N - Q := by rw [h_eq]
    _ = (A ^ N)ᵀ * Q * (A ^ N) - Q := by abel

/-- Alias for `stein_telescoping`: `Aᵀ * P_N * A - P_N = (A ^ N)ᵀ * Q * (A ^ N) - Q`. -/
theorem lyapunovSum_step (A Q : Matrix n n ℝ) (N : ℕ) :
    Aᵀ * lyapunovSum A Q N * A - lyapunovSum A Q N = (A ^ N)ᵀ * Q * (A ^ N) - Q :=
  stein_telescoping A Q N

/-- Telescoping identity in `(Aᵀ ^ N) * Q * (A ^ N)` form. -/
theorem stein_telescoping_transpose_pow (A Q : Matrix n n ℝ) (N : ℕ) :
    Aᵀ * lyapunovSum A Q N * A - lyapunovSum A Q N = (Aᵀ ^ N) * Q * (A ^ N) - Q := by
  rw [stein_telescoping, transpose_pow]

/-- Negated / dissipation-oriented Stein telescoping identity:
`P_N - Aᵀ * P_N * A = Q - (A ^ N)ᵀ * Q * (A ^ N)`. -/
theorem lyapunovSum_dissipation (A Q : Matrix n n ℝ) (N : ℕ) :
    lyapunovSum A Q N - Aᵀ * lyapunovSum A Q N * A = Q - (A ^ N)ᵀ * Q * (A ^ N) := by
  have h := stein_telescoping A Q N
  calc lyapunovSum A Q N - Aᵀ * lyapunovSum A Q N * A
      = -(Aᵀ * lyapunovSum A Q N * A - lyapunovSum A Q N) := by abel
    _ = -((A ^ N)ᵀ * Q * (A ^ N) - Q) := by rw [h]
    _ = Q - (A ^ N)ᵀ * Q * (A ^ N) := by abel

/-- Quadratic form of the `k`-th stage Lyapunov summand equals the stage cost along the trajectory:
`quad ((A ^ k)ᵀ * Q * (A ^ k)) x = quad Q ((A ^ k) *ᵥ x)`. -/
theorem quad_lyapunovTerm (A Q : Matrix n n ℝ) (k : ℕ) (x : n → ℝ) :
    quad ((A ^ k)ᵀ * Q * (A ^ k)) x = quad Q ((A ^ k) *ᵥ x) := by
  rw [← quad_mulVec]

/-- Quadratic form of `lyapunovSum` equals the finite-horizon cumulative trajectory cost:
`quad (lyapunovSum A Q N) x = ∑ k ∈ Finset.range N, quad Q ((A ^ k) *ᵥ x)`. -/
theorem quad_lyapunovSum (A Q : Matrix n n ℝ) (N : ℕ) (x : n → ℝ) :
    quad (lyapunovSum A Q N) x = ∑ k ∈ Finset.range N, quad Q ((A ^ k) *ᵥ x) := by
  unfold lyapunovSum quad
  rw [sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact quad_lyapunovTerm A Q k x

/-- **Quadratic-Form Stein Telescoping Identity** (`quad` version):
`quad (Aᵀ * P_N * A - P_N) x = quad Q ((A ^ N) *ᵥ x) - quad Q x`. -/
theorem quad_stein_telescoping (A Q : Matrix n n ℝ) (N : ℕ) (x : n → ℝ) :
    quad (Aᵀ * lyapunovSum A Q N * A - lyapunovSum A Q N) x =
      quad Q ((A ^ N) *ᵥ x) - quad Q x := by
  rw [stein_telescoping, quad_sub, quad_mulVec]

/-- **Quadratic-Form Stein Telescoping Identity** (`dotProduct` version):
`x ⬝ᵥ ((Aᵀ * P_N * A - P_N) *ᵥ x) = ((A ^ N) *ᵥ x) ⬝ᵥ (Q *ᵥ ((A ^ N) *ᵥ x)) - x ⬝ᵥ (Q *ᵥ x)`. -/
theorem dotProduct_stein_telescoping (A Q : Matrix n n ℝ) (N : ℕ) (x : n → ℝ) :
    x ⬝ᵥ ((Aᵀ * lyapunovSum A Q N * A - lyapunovSum A Q N) *ᵥ x) =
      ((A ^ N) *ᵥ x) ⬝ᵥ (Q *ᵥ ((A ^ N) *ᵥ x)) - x ⬝ᵥ (Q *ᵥ x) :=
  quad_stein_telescoping A Q N x

/-! ### 3. Symmetry & Positive-Definiteness Preservation -/

/-- If `Q` is symmetric (`Qᵀ = Q`), then every stage summand `(A ^ k)ᵀ * Q * (A ^ k)` is symmetric. -/
theorem lyapunovTerm_transpose (A Q : Matrix n n ℝ) (hQ : Qᵀ = Q) (k : ℕ) :
    ((A ^ k)ᵀ * Q * (A ^ k))ᵀ = (A ^ k)ᵀ * Q * (A ^ k) := by
  simp only [transpose_mul, transpose_transpose, hQ, Matrix.mul_assoc]

/-- **Symmetry Preservation**: If `Qᵀ = Q`, then `(lyapunovSum A Q N)ᵀ = lyapunovSum A Q N`. -/
theorem lyapunovSum_transpose (A Q : Matrix n n ℝ) (hQ : Qᵀ = Q) (N : ℕ) :
    (lyapunovSum A Q N)ᵀ = lyapunovSum A Q N := by
  unfold lyapunovSum
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun k _ => lyapunovTerm_transpose A Q hQ k

/-- If `Q` is Hermitian, then `lyapunovSum A Q N` is Hermitian. -/
theorem isHermitian_lyapunovSum (A Q : Matrix n n ℝ) (hQ : Q.IsHermitian) (N : ℕ) :
    (lyapunovSum A Q N).IsHermitian := by
  rw [ControlsLean.Tactics.isHermitian_iff_transpose_eq] at hQ ⊢
  exact lyapunovSum_transpose A Q hQ N

/-- If `Q` has non-negative quadratic form (`∀ v, 0 ≤ v ⬝ᵥ (Q *ᵥ v)`), then `lyapunovSum A Q N`
has non-negative quadratic form for all `N`. -/
theorem quad_lyapunovSum_nonneg (A Q : Matrix n n ℝ)
    (hQ : ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ (Q *ᵥ v)) (N : ℕ) (x : n → ℝ) :
    0 ≤ x ⬝ᵥ (lyapunovSum A Q N *ᵥ x) := by
  change 0 ≤ quad (lyapunovSum A Q N) x
  rw [quad_lyapunovSum]
  exact Finset.sum_nonneg fun k _ => hQ ((A ^ k) *ᵥ x)

/-- **Lower Bound by Stage Cost `Q`** (`dotProduct` version):
For `N ≥ 1` and positive semidefinite `Q` (`∀ v, 0 ≤ v ⬝ᵥ (Q *ᵥ v)`),
`x ⬝ᵥ (Q *ᵥ x) ≤ x ⬝ᵥ (lyapunovSum A Q N *ᵥ x)` for all `x`. -/
theorem quad_lyapunovSum_ge (A Q : Matrix n n ℝ)
    (hQ : ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ (Q *ᵥ v)) {N : ℕ} (hN : 1 ≤ N) (x : n → ℝ) :
    x ⬝ᵥ (Q *ᵥ x) ≤ x ⬝ᵥ (lyapunovSum A Q N *ᵥ x) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [add_comm 1 M]
  change quad Q x ≤ quad (lyapunovSum A Q (M + 1)) x
  rw [lyapunovSum_succ', ControlsLean.Tactics.quad_add, ← quad_mulVec]
  have h_nonneg : 0 ≤ quad (lyapunovSum A Q M) (A *ᵥ x) :=
    quad_lyapunovSum_nonneg A Q hQ M (A *ᵥ x)
  linarith

/-- **Lower Bound by Stage Cost `Q`** (`quad` version):
For `N ≥ 1` and `∀ v, 0 ≤ quad Q v`, `quad Q x ≤ quad (lyapunovSum A Q N) x`. -/
theorem quad_lyapunovSum_ge' (A Q : Matrix n n ℝ)
    (hQ : ∀ v : n → ℝ, 0 ≤ quad Q v) {N : ℕ} (hN : 1 ≤ N) (x : n → ℝ) :
    quad Q x ≤ quad (lyapunovSum A Q N) x :=
  quad_lyapunovSum_ge A Q hQ hN x

omit [DecidableEq n] in
/-- Helper: every `PosDef` matrix has non-negative quadratic form everywhere. -/
theorem PosDef.dotProduct_mulVec_nonneg {M : Matrix n n ℝ} (hM : M.PosDef) (v : n → ℝ) :
    0 ≤ v ⬝ᵥ (M *ᵥ v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact le_of_lt ((posDef_iff_dotProduct_mulVec.1 hM).2 hv)

/-- **Positive-Definiteness Preservation**:
If `Q` is `Matrix.PosDef` and `1 ≤ N`, then `lyapunovSum A Q N` is `Matrix.PosDef`. -/
theorem posDef_lyapunovSum (A Q : Matrix n n ℝ) (hQ : Q.PosDef) {N : ℕ} (hN : 1 ≤ N) :
    (lyapunovSum A Q N).PosDef := by
  rw [ControlsLean.Tactics.posDef_iff_dotProduct_pos] at hQ ⊢
  refine ⟨lyapunovSum_transpose A Q hQ.1 N, fun x hx => ?_⟩
  have hQ_nonneg : ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ (Q *ᵥ v) := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact le_of_lt (hQ.2 v hv)
  exact lt_of_lt_of_le (hQ.2 x hx) (quad_lyapunovSum_ge A Q hQ_nonneg hN x)

/-! ### 4. Nilpotent / Deadbeat Exact Converse Lyapunov Certificate -/

/-- Under nilpotence `A ^ N = 0`, the finite-horizon Lyapunov sum satisfies the exact
discrete-time Lyapunov equation `Aᵀ * P_N * A - P_N = -Q`. -/
theorem lyapunovSum_nilpotent_eq (A Q : Matrix n n ℝ) {N : ℕ} (hA : A ^ N = 0) :
    Aᵀ * lyapunovSum A Q N * A - lyapunovSum A Q N = -Q := by
  rw [stein_telescoping, hA]
  simp

/-- **Nilpotent / Deadbeat Converse Discrete-Time Lyapunov Theorem**:
If `A ^ N = 0` (e.g., a deadbeat closed-loop system) and `Q` is `Matrix.PosDef`,
then `P_N = lyapunovSum A Q N` is `Matrix.PosDef` and satisfies the exact discrete-time
Lyapunov equation `Aᵀ * P_N * A - P_N = -Q`. -/
theorem converse_lyapunov_nilpotent (A Q : Matrix n n ℝ) {N : ℕ}
    (hA : A ^ N = 0) (hQ : Q.PosDef) :
    (lyapunovSum A Q N).PosDef ∧ Aᵀ * lyapunovSum A Q N * A - lyapunovSum A Q N = -Q := by
  refine ⟨?_, lyapunovSum_nilpotent_eq A Q hA⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- Degenerate case N = 0: A ^ 0 = 1 = 0 implies the vector space is trivial (x = 0 for all x)
    simp only [pow_zero] at hA
    rw [ControlsLean.Tactics.posDef_iff_dotProduct_pos]
    refine ⟨by simp [lyapunovSum], fun x hx => ?_⟩
    exfalso
    apply hx
    calc x = (1 : Matrix n n ℝ) *ᵥ x := (one_mulVec x).symm
      _ = (0 : Matrix n n ℝ) *ᵥ x := by rw [hA]
      _ = 0 := zero_mulVec x
  · exact posDef_lyapunovSum A Q hQ hN

/-! ### 5. Infinite-Horizon Limit Converse Lyapunov Certificate -/

omit [Fintype n] [DecidableEq n] in
/-- Entrywise continuity helper: if `M k → P` in `Matrix n n ℝ`, then `M kᵀ → Pᵀ`. -/
theorem tendsto_transpose {M : ℕ → Matrix n n ℝ} {P : Matrix n n ℝ}
    (hP : Tendsto M atTop (𝓝 P)) :
    Tendsto (fun N => (M N)ᵀ) atTop (𝓝 Pᵀ) := by
  have hcont : Continuous (fun X : Matrix n n ℝ => Xᵀ) := by
    unfold transpose
    fun_prop
  exact (hcont.tendsto P).comp hP

omit [DecidableEq n] in
/-- Continuity helper: if `M k → P` in `Matrix n n ℝ`, then `x ⬝ᵥ (M k *ᵥ x) → x ⬝ᵥ (P *ᵥ x)`. -/
theorem tendsto_quad_of_tendsto {M : ℕ → Matrix n n ℝ} {P : Matrix n n ℝ}
    (hP : Tendsto M atTop (𝓝 P)) (x : n → ℝ) :
    Tendsto (fun N => x ⬝ᵥ (M N *ᵥ x)) atTop (𝓝 (x ⬝ᵥ (P *ᵥ x))) := by
  have hcont : Continuous (fun X : Matrix n n ℝ => x ⬝ᵥ (X *ᵥ x)) := by
    unfold dotProduct mulVec
    fun_prop
  exact (hcont.tendsto P).comp hP

omit [DecidableEq n] in
/-- Continuity helper: if `M k → P` in `Matrix n n ℝ`, then `Aᵀ * M k * A - M k → Aᵀ * P * A - P`. -/
theorem tendsto_stein_operator (A : Matrix n n ℝ) {M : ℕ → Matrix n n ℝ} {P : Matrix n n ℝ}
    (hP : Tendsto M atTop (𝓝 P)) :
    Tendsto (fun N => Aᵀ * M N * A - M N) atTop (𝓝 (Aᵀ * P * A - P)) := by
  have hcont : Continuous (fun X : Matrix n n ℝ => Aᵀ * X * A - X) := by
    fun_prop
  exact (hcont.tendsto P).comp hP

/-- **Infinite-Horizon Limit Stein / Lyapunov Equation**:
If `lyapunovSum A Q N → P` and `(A ^ N)ᵀ * Q * (A ^ N) → 0` as `N → ∞`,
then `P` satisfies the exact discrete-time Lyapunov equation `Aᵀ * P * A - P = -Q`. -/
theorem stein_eq_of_tendsto (A Q P : Matrix n n ℝ)
    (hP : Tendsto (lyapunovSum A Q) atTop (𝓝 P))
    (hA : Tendsto (fun N => (A ^ N)ᵀ * Q * (A ^ N)) atTop (𝓝 0)) :
    Aᵀ * P * A - P = -Q := by
  have h_lhs : Tendsto (fun N => Aᵀ * lyapunovSum A Q N * A - lyapunovSum A Q N)
      atTop (𝓝 (Aᵀ * P * A - P)) :=
    tendsto_stein_operator A hP
  have h_rhs : Tendsto (fun N => (A ^ N)ᵀ * Q * (A ^ N) - Q) atTop (𝓝 (-Q)) := by
    simpa [zero_sub] using hA.sub tendsto_const_nhds
  have h_eq : (fun N => Aᵀ * lyapunovSum A Q N * A - lyapunovSum A Q N) =
      (fun N => (A ^ N)ᵀ * Q * (A ^ N) - Q) := by
    ext N : 1
    exact stein_telescoping A Q N
  rw [h_eq] at h_lhs
  exact tendsto_nhds_unique h_lhs h_rhs

/-- If `lyapunovSum A Q N → P` and `Qᵀ = Q`, then the limit `P` is symmetric (`Pᵀ = P`). -/
theorem transpose_of_tendsto_lyapunovSum (A Q P : Matrix n n ℝ)
    (hQ : Qᵀ = Q) (hP : Tendsto (lyapunovSum A Q) atTop (𝓝 P)) :
    Pᵀ = P := by
  have h1 : Tendsto (fun N => (lyapunovSum A Q N)ᵀ) atTop (𝓝 Pᵀ) :=
    tendsto_transpose hP
  have h_eq : (fun N => (lyapunovSum A Q N)ᵀ) = lyapunovSum A Q := by
    ext N : 1
    exact lyapunovSum_transpose A Q hQ N
  rw [h_eq] at h1
  exact tendsto_nhds_unique h1 hP

/-- If `lyapunovSum A Q N → P` and `∀ v, 0 ≤ v ⬝ᵥ (Q *ᵥ v)`, then `x ⬝ᵥ (Q *ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x)`
for all `x`. -/
theorem quad_ge_of_tendsto_lyapunovSum (A Q P : Matrix n n ℝ)
    (hQ : ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ (Q *ᵥ v))
    (hP : Tendsto (lyapunovSum A Q) atTop (𝓝 P)) (x : n → ℝ) :
    x ⬝ᵥ (Q *ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x) := by
  have h_quad : Tendsto (fun N => x ⬝ᵥ (lyapunovSum A Q N *ᵥ x)) atTop (𝓝 (x ⬝ᵥ (P *ᵥ x))) :=
    tendsto_quad_of_tendsto hP x
  refine ge_of_tendsto h_quad ?_
  rw [eventually_atTop]
  exact ⟨1, fun N hN => quad_lyapunovSum_ge A Q hQ hN x⟩

/-- If `lyapunovSum A Q N → P` and `Q` is `Matrix.PosDef`, then the limit `P` is `Matrix.PosDef`. -/
theorem posDef_of_tendsto_lyapunovSum (A Q P : Matrix n n ℝ)
    (hQ : Q.PosDef) (hP : Tendsto (lyapunovSum A Q) atTop (𝓝 P)) :
    P.PosDef := by
  rw [ControlsLean.Tactics.posDef_iff_dotProduct_pos] at hQ ⊢
  have hQ_nonneg : ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ (Q *ᵥ v) := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact le_of_lt (hQ.2 v hv)
  refine ⟨transpose_of_tendsto_lyapunovSum A Q P hQ.1 hP, fun x hx => ?_⟩
  exact lt_of_lt_of_le (hQ.2 x hx) (quad_ge_of_tendsto_lyapunovSum A Q P hQ_nonneg hP x)

/-- **Infinite-Horizon Converse Discrete-Time Lyapunov Theorem** (general positive semidefinite form):
If `lyapunovSum A Q N → P` and `(A ^ N)ᵀ * Q * (A ^ N) → 0` as `N → ∞`,
and `Q` is symmetric positive semidefinite (`Qᵀ = Q` and `∀ v, 0 ≤ v ⬝ᵥ (Q *ᵥ v)`),
then `P` satisfies:
1. `Aᵀ * P * A - P = -Q`,
2. `Pᵀ = P`,
3. `∀ x, x ⬝ᵥ (Q *ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x)`. -/
theorem converse_lyapunov_of_tendsto_semidef (A Q P : Matrix n n ℝ)
    (hP : Tendsto (lyapunovSum A Q) atTop (𝓝 P))
    (hA : Tendsto (fun N => (A ^ N)ᵀ * Q * (A ^ N)) atTop (𝓝 0))
    (hQ_symm : Qᵀ = Q) (hQ_nonneg : ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ (Q *ᵥ v)) :
    (Aᵀ * P * A - P = -Q) ∧ Pᵀ = P ∧ (∀ x : n → ℝ, x ⬝ᵥ (Q *ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x)) :=
  ⟨stein_eq_of_tendsto A Q P hP hA,
   transpose_of_tendsto_lyapunovSum A Q P hQ_symm hP,
   quad_ge_of_tendsto_lyapunovSum A Q P hQ_nonneg hP⟩

/-- **Infinite-Horizon Converse Discrete-Time Lyapunov Theorem** (`PosDef` certificate form):
If `lyapunovSum A Q N → P` and `(A ^ N)ᵀ * Q * (A ^ N) → 0` as `N → ∞`,
and `Q` is `Matrix.PosDef`, then `P` is `Matrix.PosDef`, satisfies the exact discrete-time
Lyapunov equation `Aᵀ * P * A - P = -Q`, and dominates `Q` (`∀ x, x ⬝ᵥ (Q *ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x)`). -/
theorem converse_lyapunov_of_tendsto (A Q P : Matrix n n ℝ)
    (hP : Tendsto (lyapunovSum A Q) atTop (𝓝 P))
    (hA : Tendsto (fun N => (A ^ N)ᵀ * Q * (A ^ N)) atTop (𝓝 0))
    (hQ : Q.PosDef) :
    P.PosDef ∧ Aᵀ * P * A - P = -Q ∧ (∀ x : n → ℝ, x ⬝ᵥ (Q *ᵥ x) ≤ x ⬝ᵥ (P *ᵥ x)) :=
  ⟨posDef_of_tendsto_lyapunovSum A Q P hQ hP,
   stein_eq_of_tendsto A Q P hP hA,
   quad_ge_of_tendsto_lyapunovSum A Q P (PosDef.dotProduct_mulVec_nonneg hQ) hP⟩

/-- **Bidirectional Bridge (Direct + Converse Lyapunov Equivalence)**:
When `P` is obtained as the infinite-horizon Lyapunov limit for `Q.PosDef`, `P` directly
certifies global asymptotic stability `A ^ k *ᵥ x₀ → 0` via `PosDef.tendsto_pow_mulVec_zero`. -/
theorem tendsto_pow_mulVec_zero_of_converse_lyapunov (A Q P : Matrix n n ℝ)
    (hP : Tendsto (lyapunovSum A Q) atTop (𝓝 P))
    (hA : Tendsto (fun N => (A ^ N)ᵀ * Q * (A ^ N)) atTop (𝓝 0))
    (hQ : Q.PosDef) (x₀ : n → ℝ) :
    Tendsto (fun k : ℕ => (A ^ k) *ᵥ x₀) atTop (𝓝 0) := by
  obtain ⟨hP_pos, h_stein, _⟩ := converse_lyapunov_of_tendsto A Q P hP hA hQ
  have h_sub : P - Aᵀ * P * A = Q := by
    calc P - Aᵀ * P * A = -(Aᵀ * P * A - P) := by abel
      _ = -(-Q) := by rw [h_stein]
      _ = Q := neg_neg Q
  have h_diff_pos : (P - Aᵀ * P * A).PosDef := by
    rw [h_sub]
    exact hQ
  exact PosDef.tendsto_pow_mulVec_zero hP_pos h_diff_pos x₀

end ControlsLean.Controls
