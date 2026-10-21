/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Model Predictive Control: Recursive Feasibility and Value Function Descent

This module formalizes constrained discrete-time Model Predictive Control (MPC)
following Rawlings, Mayne, and Diehl (2017). Given discrete-time dynamics
`step : X → U → X`, state constraint set `X_adm : Set X`, input constraint set
`U_adm : Set U`, and terminal constraint set `X_f : Set X`:

1. **Control Invariant Terminal Set (`IsControlInvariant`)**:
   A terminal set `X_f ⊆ X_adm` equipped with a local terminal control law `κ_f : X → U`
   such that for all `x ∈ X_f`, `κ_f x ∈ U_adm` and `step x (κ_f x) ∈ X_f`.

2. **Horizon-`N` Admissible Trajectory (`IsAdmissibleHorizon`)**:
   An open-loop input plan `u : ℕ → U` from initial state `x₀ : X` is admissible over
   prediction horizon `N` if all predicted states `x_k` (`k < N`) lie in `X_adm`,
   all inputs `u_k` (`k < N`) lie in `U_adm`, and the terminal state `x_N` lies in `X_f`.

3. **One-Step Recursive Feasibility (`mpc_recursive_feasibility_step`)**:
   If `u` is horizon-`N` admissible from `x₀` (`0 < N`), then the warm-start shifted
   input sequence `shiftInput step κ_f N x₀ u` defined by `u'(k) = u(k + 1)` for
   `k < N - 1` and `u'(N - 1) = κ_f(x_N)` is horizon-`N` admissible from the successor
   state `x₁ = step x₀ (u 0)`.

4. **Eternal Closed-Loop Feasibility (`mpc_closed_loop_feasible`)**:
   From any initially feasible state `x₀`, any receding-horizon MPC policy `μ : X → (ℕ → U)`
   that selects an admissible plan whenever one exists remains recursively feasible at every
   future step `t ∈ ℕ` and satisfies state and input constraints `x_t ∈ X_adm` and
   `u_t ∈ U_adm` for all `t ∈ ℕ`.

5. **MPC Value Function Lyapunov Descent (`mpc_value_descent`)**:
   If the terminal cost `V_f : X → ℝ` and stage cost `ℓ : X → U → ℝ` satisfy the terminal
   Control Lyapunov Function (CLF) condition `V_f (step x (κ_f x)) + ℓ x (κ_f x) ≤ V_f x`
   on `X_f`, then the horizon-`N` cost `mpcCost` of the shifted candidate trajectory satisfies:
   `mpcCost step ℓ V_f N (step x₀ (u 0)) (shiftInput step κ_f N x₀ u) ≤ mpcCost step ℓ V_f N x₀ u - ℓ x₀ (u 0)`.

## References

* Rawlings, J. B., Mayne, D. Q., & Diehl, M. (2017). *Model Predictive Control: Theory,
  Computation, and Design* (2nd ed.). Nob Hill Publishing. Chapter 2, Sections 2.4–2.5.
* Mayne, D. Q., Rawlings, J. B., Rao, C. V., & Scokaert, P. O. M. (2000). Constrained model
  predictive control: Stability and optimality. *Automatica*, 36(6): 789–814.
* Keerthi, S. S., & Gilbert, E. G. (1988). Optimal infinite-horizon feedback laws for a general
  class of constrained discrete-time systems: Stability and moving-horizon approximations.
  *Journal of Optimization Theory and Applications*, 57(2): 265–293.
-/

namespace ControlsLean.Controls

open BigOperators Matrix

variable {X U : Type*}

/-! ### Open-Loop Prediction Dynamics and Warm-Start Shifting -/

/-- Open-loop state trajectory predicted from initial state `x₀` under input sequence `u`
and discrete-time transition map `step : X → U → X`. -/
def mpcTraj (step : X → U → X) (x₀ : X) (u : ℕ → U) : ℕ → X
  | 0 => x₀
  | k + 1 => step (mpcTraj step x₀ u k) (u k)

@[simp]
theorem mpcTraj_zero (step : X → U → X) (x₀ : X) (u : ℕ → U) :
    mpcTraj step x₀ u 0 = x₀ := rfl

@[simp]
theorem mpcTraj_succ (step : X → U → X) (x₀ : X) (u : ℕ → U) (k : ℕ) :
    mpcTraj step x₀ u (k + 1) = step (mpcTraj step x₀ u k) (u k) := rfl

/-- Time-shift invariance of `mpcTraj`: starting from `step x₀ (u 0)` with shifted inputs
`fun j => u (j + 1)` reproduces `mpcTraj step x₀ u (k + 1)`. -/
theorem mpcTraj_shift (step : X → U → X) (x₀ : X) (u : ℕ → U) (k : ℕ) :
    mpcTraj step (step x₀ (u 0)) (fun j => u (j + 1)) k = mpcTraj step x₀ u (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [mpcTraj_succ, ih]

/-- The state at prediction step `k` depends only on the first `k` control inputs `u 0, ..., u (k - 1)`. -/
theorem mpcTraj_congr (step : X → U → X) (x₀ : X) {u₁ u₂ : ℕ → U} {k : ℕ}
    (h : ∀ j < k, u₁ j = u₂ j) :
    mpcTraj step x₀ u₁ k = mpcTraj step x₀ u₂ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [mpcTraj_succ]
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h k (Nat.lt_succ_self k)]

/-- The standard MPC warm-start shifted input sequence for horizon `N`:
`u'(k) = u(k + 1)` for `k + 1 < N` (i.e., `k < N - 1`), and `u'(k) = κ_f(x_N)` at `k = N - 1`
(and beyond). -/
def shiftInput (step : X → U → X) (κ_f : X → U) (N : ℕ) (x₀ : X) (u : ℕ → U) (k : ℕ) : U :=
  if k + 1 < N then u (k + 1) else κ_f (mpcTraj step x₀ u N)

theorem shiftInput_of_lt (step : X → U → X) (κ_f : X → U) (N : ℕ) (x₀ : X) (u : ℕ → U)
    {k : ℕ} (hk : k + 1 < N) :
    shiftInput step κ_f N x₀ u k = u (k + 1) := by
  unfold shiftInput
  simp [hk]

theorem shiftInput_of_lt_sub_one (step : X → U → X) (κ_f : X → U) (N : ℕ) (x₀ : X) (u : ℕ → U)
    {k : ℕ} (hk : k < N - 1) :
    shiftInput step κ_f N x₀ u k = u (k + 1) :=
  shiftInput_of_lt step κ_f N x₀ u (by omega)

theorem shiftInput_of_not_lt (step : X → U → X) (κ_f : X → U) (N : ℕ) (x₀ : X) (u : ℕ → U)
    {k : ℕ} (hk : ¬(k + 1 < N)) :
    shiftInput step κ_f N x₀ u k = κ_f (mpcTraj step x₀ u N) := by
  unfold shiftInput
  simp [hk]

@[simp]
theorem shiftInput_pred (step : X → U → X) (κ_f : X → U) (N : ℕ) (x₀ : X) (u : ℕ → U) :
    shiftInput step κ_f N x₀ u (N - 1) = κ_f (mpcTraj step x₀ u N) :=
  shiftInput_of_not_lt step κ_f N x₀ u (by omega)

/-- Along the shifted input sequence `shiftInput`, the predicted state at step `k` (for `k + 1 ≤ N`)
from `step x₀ (u 0)` equals the original predicted state at step `k + 1`. -/
theorem mpcTraj_shiftInput_of_le (step : X → U → X) (κ_f : X → U) (N : ℕ) (x₀ : X) (u : ℕ → U)
    {k : ℕ} (hk : k + 1 ≤ N) :
    mpcTraj step (step x₀ (u 0)) (shiftInput step κ_f N x₀ u) k =
      mpcTraj step x₀ u (k + 1) := by
  rw [mpcTraj_congr step (step x₀ (u 0)) (u₂ := fun j => u (j + 1))]
  · exact mpcTraj_shift step x₀ u k
  · intro j hj
    exact shiftInput_of_lt step κ_f N x₀ u (by omega)

/-- The terminal state at horizon `N` (`0 < N`) of the shifted candidate trajectory from
`step x₀ (u 0)` is obtained by applying the terminal control law `κ_f` to `x_N`. -/
theorem mpcTraj_shiftInput_terminal (step : X → U → X) (κ_f : X → U) {N : ℕ} (hN : 0 < N)
    (x₀ : X) (u : ℕ → U) :
    mpcTraj step (step x₀ (u 0)) (shiftInput step κ_f N x₀ u) N =
      step (mpcTraj step x₀ u N) (κ_f (mpcTraj step x₀ u N)) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hN)
  rw [mpcTraj_succ, mpcTraj_shiftInput_of_le step κ_f (M + 1) x₀ u (le_refl (M + 1)),
      shiftInput_of_not_lt step κ_f (M + 1) x₀ u (Nat.lt_irrefl (M + 1))]

/-! ### Constraints, Control Invariance, and Recursive Feasibility -/

/-- A terminal constraint set `X_f` is **control invariant** under terminal control law `κ_f`
if `X_f ⊆ X_adm` and for every `x ∈ X_f`, the terminal input `κ_f x` is admissible (`∈ U_adm`)
and keeps the successor state `step x (κ_f x)` inside `X_f`. -/
structure IsControlInvariant (step : X → U → X) (X_adm : Set X) (U_adm : Set U)
    (X_f : Set X) (κ_f : X → U) : Prop where
  subset_adm : X_f ⊆ X_adm
  input_adm : ∀ x ∈ X_f, κ_f x ∈ U_adm
  step_mem : ∀ x ∈ X_f, step x (κ_f x) ∈ X_f

/-- An input sequence `u : ℕ → U` is **horizon-`N` admissible** from initial state `x₀` if
all predicted states for `k < N` lie in `X_adm`, all inputs for `k < N` lie in `U_adm`,
and the terminal state at step `N` lies in `X_f`. -/
structure IsAdmissibleHorizon (step : X → U → X) (X_adm : Set X) (U_adm : Set U)
    (X_f : Set X) (N : ℕ) (x₀ : X) (u : ℕ → U) : Prop where
  state_adm : ∀ k < N, mpcTraj step x₀ u k ∈ X_adm
  input_adm : ∀ k < N, u k ∈ U_adm
  terminal_mem : mpcTraj step x₀ u N ∈ X_f

/-- Under a control invariant terminal set `X_f ⊆ X_adm`, any horizon-`N` admissible trajectory
satisfies state constraints at all `k ≤ N` (including the terminal state `k = N`). -/
theorem IsAdmissibleHorizon.state_adm_of_le {step : X → U → X} {X_adm : Set X} {U_adm : Set U}
    {X_f : Set X} {κ_f : X → U} {N : ℕ} {x₀ : X} {u : ℕ → U}
    (hinv : IsControlInvariant step X_adm U_adm X_f κ_f)
    (hu : IsAdmissibleHorizon step X_adm U_adm X_f N x₀ u)
    {k : ℕ} (hk : k ≤ N) :
    mpcTraj step x₀ u k ∈ X_adm := by
  rcases Nat.lt_or_eq_of_le hk with hlt | rfl
  · exact hu.state_adm k hlt
  · exact hinv.subset_adm hu.terminal_mem

/-- **Headline Theorem 1 — One-Step MPC Recursive Feasibility**:
If `X_f` is control invariant under `κ_f` and `u` is horizon-`N` admissible from `x₀` (`0 < N`),
then the shifted candidate sequence `shiftInput step κ_f N x₀ u` is horizon-`N` admissible
from the successor state `step x₀ (u 0)`. -/
theorem mpc_recursive_feasibility_step {step : X → U → X} {X_adm : Set X} {U_adm : Set U}
    {X_f : Set X} {κ_f : X → U} {N : ℕ} (hN : 0 < N)
    (hinv : IsControlInvariant step X_adm U_adm X_f κ_f)
    {x₀ : X} {u : ℕ → U}
    (hu : IsAdmissibleHorizon step X_adm U_adm X_f N x₀ u) :
    IsAdmissibleHorizon step X_adm U_adm X_f N
      (step x₀ (u 0)) (shiftInput step κ_f N x₀ u) where
  state_adm k hk := by
    rw [mpcTraj_shiftInput_of_le step κ_f N x₀ u (by omega)]
    exact hu.state_adm_of_le hinv (by omega)
  input_adm k hk := by
    by_cases hk1 : k + 1 < N
    · rw [shiftInput_of_lt step κ_f N x₀ u hk1]
      exact hu.input_adm (k + 1) hk1
    · rw [shiftInput_of_not_lt step κ_f N x₀ u hk1]
      exact hinv.input_adm _ hu.terminal_mem
  terminal_mem := by
    rw [mpcTraj_shiftInput_terminal step κ_f hN x₀ u]
    exact hinv.step_mem _ hu.terminal_mem

/-! ### Eternal Closed-Loop MPC Feasibility -/

/-- A state `x` is horizon-`N` feasible if there exists at least one horizon-`N` admissible
control sequence starting from `x`. -/
def IsFeasibleState (step : X → U → X) (X_adm : Set X) (U_adm : Set U)
    (X_f : Set X) (N : ℕ) (x : X) : Prop :=
  ∃ u : ℕ → U, IsAdmissibleHorizon step X_adm U_adm X_f N x u

/-- Applying the first control input `u 0` of any horizon-`N` admissible sequence `u` from `x`
transitions to a horizon-`N` feasible successor state `step x (u 0)`. -/
theorem mpc_feasible_step {step : X → U → X} {X_adm : Set X} {U_adm : Set U}
    {X_f : Set X} {κ_f : X → U} {N : ℕ} (hN : 0 < N)
    (hinv : IsControlInvariant step X_adm U_adm X_f κ_f)
    {x : X} {u : ℕ → U}
    (hu : IsAdmissibleHorizon step X_adm U_adm X_f N x u) :
    IsFeasibleState step X_adm U_adm X_f N (step x (u 0)) :=
  ⟨shiftInput step κ_f N x u, mpc_recursive_feasibility_step hN hinv hu⟩

/-- A receding-horizon policy `μ : X → (ℕ → U)` is an admissible MPC feedback selector if
it returns a horizon-`N` admissible plan whenever the current state `x` is feasible. -/
def IsAdmissibleMPCPolicy (step : X → U → X) (X_adm : Set X) (U_adm : Set U)
    (X_f : Set X) (N : ℕ) (μ : X → (ℕ → U)) : Prop :=
  ∀ x, IsFeasibleState step X_adm U_adm X_f N x →
    IsAdmissibleHorizon step X_adm U_adm X_f N x (μ x)

/-- Closed-loop state trajectory under receding-horizon MPC policy `μ : X → (ℕ → U)`,
applying the first element `μ x 0` at each state `x`. -/
def mpcClosedLoopTraj (step : X → U → X) (μ : X → (ℕ → U)) (x₀ : X) : ℕ → X
  | 0 => x₀
  | t + 1 => step (mpcClosedLoopTraj step μ x₀ t) (μ (mpcClosedLoopTraj step μ x₀ t) 0)

@[simp]
theorem mpcClosedLoopTraj_zero (step : X → U → X) (μ : X → (ℕ → U)) (x₀ : X) :
    mpcClosedLoopTraj step μ x₀ 0 = x₀ := rfl

@[simp]
theorem mpcClosedLoopTraj_succ (step : X → U → X) (μ : X → (ℕ → U)) (x₀ : X) (t : ℕ) :
    mpcClosedLoopTraj step μ x₀ (t + 1) =
      step (mpcClosedLoopTraj step μ x₀ t) (μ (mpcClosedLoopTraj step μ x₀ t) 0) := rfl

/-- **Headline Theorem 2 — Eternal Closed-Loop MPC Feasibility**:
From any initially feasible state `x₀`, the receding-horizon closed-loop trajectory under any
admissible MPC selector `μ` remains feasible at every future step `t ∈ ℕ` and satisfies
both state constraints (`x_t ∈ X_adm`) and input constraints (`μ x_t 0 ∈ U_adm`) for all `t ∈ ℕ`. -/
theorem mpc_closed_loop_feasible {step : X → U → X} {X_adm : Set X} {U_adm : Set U}
    {X_f : Set X} {κ_f : X → U} {N : ℕ} (hN : 0 < N)
    (hinv : IsControlInvariant step X_adm U_adm X_f κ_f)
    {μ : X → (ℕ → U)} (hμ : IsAdmissibleMPCPolicy step X_adm U_adm X_f N μ)
    {x₀ : X} (hx₀ : IsFeasibleState step X_adm U_adm X_f N x₀) (t : ℕ) :
    IsFeasibleState step X_adm U_adm X_f N (mpcClosedLoopTraj step μ x₀ t) ∧
      mpcClosedLoopTraj step μ x₀ t ∈ X_adm ∧
      μ (mpcClosedLoopTraj step μ x₀ t) 0 ∈ U_adm := by
  have h_feas : ∀ k : ℕ, IsFeasibleState step X_adm U_adm X_f N (mpcClosedLoopTraj step μ x₀ k) := by
    intro k
    induction k with
    | zero => exact hx₀
    | succ k ih =>
      simp only [mpcClosedLoopTraj_succ]
      exact mpc_feasible_step hN hinv (hμ _ ih)
  have ht_feas := h_feas t
  have ht_adm := hμ _ ht_feas
  exact ⟨ht_feas, ht_adm.state_adm 0 hN, ht_adm.input_adm 0 hN⟩

/-! ### MPC Cost Functional and Lyapunov Value Descent -/

/-- The finite-horizon MPC cost functional:
$$J_N(x_0, u) = \sum_{k=0}^{N-1} \ell(x_k, u_k) + V_f(x_N).$$ -/
def mpcCost (step : X → U → X) (ℓ : X → U → ℝ) (V_f : X → ℝ)
    (N : ℕ) (x₀ : X) (u : ℕ → U) : ℝ :=
  (∑ k ∈ Finset.range N, ℓ (mpcTraj step x₀ u k) (u k)) + V_f (mpcTraj step x₀ u N)

/-- A terminal cost function `V_f : X → ℝ` is a **terminal Control Lyapunov Function (CLF)** on `X_f`
under terminal law `κ_f` and stage cost `ℓ` if for all `x ∈ X_f`,
`V_f (step x (κ_f x)) + ℓ x (κ_f x) ≤ V_f x`. -/
def IsTerminalCLF (step : X → U → X) (ℓ : X → U → ℝ) (V_f : X → ℝ)
    (X_f : Set X) (κ_f : X → U) : Prop :=
  ∀ x ∈ X_f, V_f (step x (κ_f x)) + ℓ x (κ_f x) ≤ V_f x

/-- Exact algebraic decomposition of the horizon-`N` cost of the shifted candidate trajectory
`shiftInput step κ_f N x₀ u` from `step x₀ (u 0)`:
$$J_N(x_1, u') = J_N(x_0, u) - \ell(x_0, u_0) +
  \bigl(V_f(\mathrm{step}(x_N, \kappa_f(x_N))) + \ell(x_N, \kappa_f(x_N)) - V_f(x_N)\bigr).$$ -/
theorem mpcCost_shiftInput_eq (step : X → U → X) (ℓ : X → U → ℝ) (V_f : X → ℝ)
    (κ_f : X → U) {N : ℕ} (hN : 0 < N) (x₀ : X) (u : ℕ → U) :
    mpcCost step ℓ V_f N (step x₀ (u 0)) (shiftInput step κ_f N x₀ u) =
      mpcCost step ℓ V_f N x₀ u - ℓ x₀ (u 0) +
        (V_f (step (mpcTraj step x₀ u N) (κ_f (mpcTraj step x₀ u N))) +
          ℓ (mpcTraj step x₀ u N) (κ_f (mpcTraj step x₀ u N)) -
          V_f (mpcTraj step x₀ u N)) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hN)
  unfold mpcCost
  have h_orig_sum : ∑ k ∈ Finset.range (M + 1), ℓ (mpcTraj step x₀ u k) (u k) =
      (∑ k ∈ Finset.range M, ℓ (mpcTraj step x₀ u (k + 1)) (u (k + 1))) +
        ℓ x₀ (u 0) :=
    Finset.sum_range_succ' (fun k => ℓ (mpcTraj step x₀ u k) (u k)) M
  have h_shift_sum :
      ∑ k ∈ Finset.range (M + 1),
        ℓ (mpcTraj step (step x₀ (u 0)) (shiftInput step κ_f (M + 1) x₀ u) k)
          (shiftInput step κ_f (M + 1) x₀ u k) =
      (∑ k ∈ Finset.range M, ℓ (mpcTraj step x₀ u (k + 1)) (u (k + 1))) +
        ℓ (mpcTraj step x₀ u (M + 1)) (κ_f (mpcTraj step x₀ u (M + 1))) := by
    rw [Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk_lt : k + 1 < M + 1 := by
        rw [Finset.mem_range] at hk
        omega
      rw [mpcTraj_shiftInput_of_le step κ_f (M + 1) x₀ u (by omega),
          shiftInput_of_lt step κ_f (M + 1) x₀ u hk_lt]
    · rw [mpcTraj_shiftInput_of_le step κ_f (M + 1) x₀ u (le_refl (M + 1)),
          shiftInput_of_not_lt step κ_f (M + 1) x₀ u (Nat.lt_irrefl (M + 1))]
  rw [h_orig_sum, h_shift_sum, mpcTraj_shiftInput_terminal step κ_f hN x₀ u]
  ring

/-- **Headline Theorem 3 — MPC Value Function Lyapunov Descent**:
If the terminal cost `V_f` and stage cost `ℓ` satisfy the terminal Control Lyapunov inequality
`V_f (step x (κ_f x)) + ℓ x (κ_f x) ≤ V_f x` on `X_f`, then for any horizon-`N` admissible
trajectory `u` from `x₀` (`0 < N`), the cost of the shifted candidate trajectory from
`x₁ = step x₀ (u 0)` satisfies:
$$J_N(x_1, u') \le J_N(x_0, u) - \ell(x_0, u_0).$$ -/
theorem mpc_value_descent {step : X → U → X} {X_adm : Set X} {U_adm : Set U}
    {X_f : Set X} {κ_f : X → U} {ℓ : X → U → ℝ} {V_f : X → ℝ}
    {N : ℕ} (hN : 0 < N)
    (hclf : IsTerminalCLF step ℓ V_f X_f κ_f)
    {x₀ : X} {u : ℕ → U}
    (hu : IsAdmissibleHorizon step X_adm U_adm X_f N x₀ u) :
    mpcCost step ℓ V_f N (step x₀ (u 0)) (shiftInput step κ_f N x₀ u) ≤
      mpcCost step ℓ V_f N x₀ u - ℓ x₀ (u 0) := by
  rw [mpcCost_shiftInput_eq step ℓ V_f κ_f hN x₀ u]
  have hterm := hclf (mpcTraj step x₀ u N) hu.terminal_mem
  linarith

/-- An MPC policy `μ : X → (ℕ → U)` is **horizon-`N` optimal** if it is an admissible selector
and minimizes `mpcCost` among all horizon-`N` admissible control sequences at every feasible state. -/
structure IsOptimalMPCPolicy (step : X → U → X) (X_adm : Set X) (U_adm : Set U)
    (X_f : Set X) (ℓ : X → U → ℝ) (V_f : X → ℝ) (N : ℕ) (μ : X → (ℕ → U)) : Prop where
  admissible : IsAdmissibleMPCPolicy step X_adm U_adm X_f N μ
  minimal : ∀ x u, IsAdmissibleHorizon step X_adm U_adm X_f N x u →
    mpcCost step ℓ V_f N x (μ x) ≤ mpcCost step ℓ V_f N x u

/-- **Optimal Value Function One-Step Lyapunov Decrease**:
Under an optimal MPC policy `μ`, the optimal value function `V_N*(x) = J_N(x, μ x)` decreases
by at least the stage cost `ℓ x (μ x 0)` along one closed-loop step:
$$V_N^*(\mathrm{step}(x, \mu(x)_0)) \le V_N^*(x) - \ell(x, \mu(x)_0).$$ -/
theorem mpc_optimal_value_descent {step : X → U → X} {X_adm : Set X} {U_adm : Set U}
    {X_f : Set X} {κ_f : X → U} {ℓ : X → U → ℝ} {V_f : X → ℝ}
    {N : ℕ} (hN : 0 < N)
    (hinv : IsControlInvariant step X_adm U_adm X_f κ_f)
    (hclf : IsTerminalCLF step ℓ V_f X_f κ_f)
    {μ : X → (ℕ → U)} (hopt : IsOptimalMPCPolicy step X_adm U_adm X_f ℓ V_f N μ)
    {x : X} (hx : IsFeasibleState step X_adm U_adm X_f N x) :
    mpcCost step ℓ V_f N (step x (μ x 0)) (μ (step x (μ x 0))) ≤
      mpcCost step ℓ V_f N x (μ x) - ℓ x (μ x 0) := by
  have hu := hopt.admissible x hx
  have hshift_adm := mpc_recursive_feasibility_step hN hinv hu
  calc mpcCost step ℓ V_f N (step x (μ x 0)) (μ (step x (μ x 0)))
    _ ≤ mpcCost step ℓ V_f N (step x (μ x 0)) (shiftInput step κ_f N x (μ x)) :=
      hopt.minimal _ _ hshift_adm
    _ ≤ mpcCost step ℓ V_f N x (μ x) - ℓ x (μ x 0) :=
      mpc_value_descent hN hclf hu

/-- **Closed-Loop Cumulative Stage Cost Bound**:
Along the closed-loop trajectory `x_t = mpcClosedLoopTraj step μ x₀ t` of an optimal MPC policy,
the cumulative stage cost over any `T` steps is bounded by the drop in optimal value:
$$\sum_{t=0}^{T-1} \ell(x_t, \mu(x_t)_0) \le V_N^*(x_0) - V_N^*(x_T).$$ -/
theorem mpc_closed_loop_cost_bound {step : X → U → X} {X_adm : Set X} {U_adm : Set U}
    {X_f : Set X} {κ_f : X → U} {ℓ : X → U → ℝ} {V_f : X → ℝ}
    {N : ℕ} (hN : 0 < N)
    (hinv : IsControlInvariant step X_adm U_adm X_f κ_f)
    (hclf : IsTerminalCLF step ℓ V_f X_f κ_f)
    {μ : X → (ℕ → U)} (hopt : IsOptimalMPCPolicy step X_adm U_adm X_f ℓ V_f N μ)
    {x₀ : X} (hx₀ : IsFeasibleState step X_adm U_adm X_f N x₀) (T : ℕ) :
    (∑ t ∈ Finset.range T,
      ℓ (mpcClosedLoopTraj step μ x₀ t) (μ (mpcClosedLoopTraj step μ x₀ t) 0)) ≤
      mpcCost step ℓ V_f N x₀ (μ x₀) -
        mpcCost step ℓ V_f N (mpcClosedLoopTraj step μ x₀ T)
          (μ (mpcClosedLoopTraj step μ x₀ T)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, mpcClosedLoopTraj_succ]
    have hT_feas := (mpc_closed_loop_feasible hN hinv hopt.admissible hx₀ T).1
    have h_step := mpc_optimal_value_descent hN hinv hclf hopt hT_feas
    linarith

/-! ### Specialization to Linear Time-Invariant (LTI) Systems -/

variable {n m : Type*} [Fintype n] [Fintype m]

/-- Discrete-time linear time-invariant (LTI) state transition `f(x, u) = A x + B u`. -/
def ltiStep (A : Matrix n n ℝ) (B : Matrix n m ℝ) (x : n → ℝ) (u : m → ℝ) : n → ℝ :=
  A *ᵥ x + B *ᵥ u

/-- One-step recursive feasibility specialized to constrained LTI systems `x_{k+1} = A x_k + B u_k`. -/
theorem lti_mpc_recursive_feasibility_step (A : Matrix n n ℝ) (B : Matrix n m ℝ)
    {X_adm : Set (n → ℝ)} {U_adm : Set (m → ℝ)}
    {X_f : Set (n → ℝ)} {κ_f : (n → ℝ) → (m → ℝ)} {N : ℕ} (hN : 0 < N)
    (hinv : IsControlInvariant (ltiStep A B) X_adm U_adm X_f κ_f)
    {x₀ : n → ℝ} {u : ℕ → (m → ℝ)}
    (hu : IsAdmissibleHorizon (ltiStep A B) X_adm U_adm X_f N x₀ u) :
    IsAdmissibleHorizon (ltiStep A B) X_adm U_adm X_f N
      (ltiStep A B x₀ (u 0)) (shiftInput (ltiStep A B) κ_f N x₀ u) :=
  mpc_recursive_feasibility_step hN hinv hu

end ControlsLean.Controls
