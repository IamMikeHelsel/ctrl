# Constrained Model Predictive Control: Recursive Feasibility and Value Function Lyapunov Descent in Lean 4

**Author**: Mike Helsel  
**Date**: October 18, 2026  
**Status**: Machine-Checked & Verified (`ControlsLean.Controls.MPCFeasibility`)  
**Target Repository**: `ctrl` (`ControlsLean/Controls/MPCFeasibility.lean`)  
**Axiom Footprint**: Standard Lean 4 axioms only (`[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero custom axioms)

---

## 1. Abstract

We present a machine-checked formalization in Lean 4 of constrained discrete-time Model Predictive Control (MPC), establishing the two foundational theoretical pillars of receding-horizon optimal control: **recursive feasibility** (persistent constraint satisfaction) and **value function Lyapunov descent** (closed-loop cost dissipation).

In constrained MPC, at each sampling instant $t \in \mathbb{N}$ with current state $x_t \in X$, the controller solves a finite-horizon optimal control problem over prediction horizon $N \ge 1$:
$$\min_{u_0, \dots, u_{N-1}} J_N(x_t, u) = \sum_{k=0}^{N-1} \ell(x_{k|t}, u_{k|t}) + V_f(x_{N|t})$$
subject to discrete-time dynamics $x_{k+1|t} = \mathrm{step}(x_{k|t}, u_{k|t})$ with $x_{0|t} = x_t$, pointwise state and input constraints $x_{k|t} \in X_{\mathrm{adm}}$ and $u_{k|t} \in U_{\mathrm{adm}}$ for $0 \le k < N$, and a terminal state constraint $x_{N|t} \in X_f$. Only the first control action $u_{0|t}$ is applied to the plant, and the optimization is repeated at $t + 1$ from $x_{t+1} = \mathrm{step}(x_t, u_{0|t})$.

Because the optimization horizon is finite, naive receding-horizon control can steer the system into states from which no constraint-satisfying trajectory exists at future steps, or exhibit closed-loop instability despite open-loop optimality. Following the canonical terminal-constraint/terminal-cost framework of Rawlings, Mayne, and Diehl (2017) and Mayne et al. (2000), we formalize:
1. **Control Invariant Terminal Sets (`IsControlInvariant`)**: $X_f \subseteq X_{\mathrm{adm}}$ equipped with a local control law $\kappa_f : X \to U$ such that $\forall x \in X_f, \kappa_f(x) \in U_{\mathrm{adm}} \land \mathrm{step}(x, \kappa_f(x)) \in X_f$.
2. **One-Step Warm-Start Recursive Feasibility (`mpc_recursive_feasibility_step`)**: Given any horizon-$N$ admissible sequence $u$ from $x_0$, the shifted candidate sequence $u'(k) = u(k+1)$ for $k < N - 1$ and $u'(N - 1) = \kappa_f(x_N)$ is horizon-$N$ admissible from the successor state $x_1 = \mathrm{step}(x_0, u_0)$.
3. **Eternal Closed-Loop Feasibility (`mpc_closed_loop_feasible`)**: From any initially feasible state $x_0$, the closed-loop trajectory under any admissible receding-horizon MPC policy $\mu$ remains feasible at every future step $t \in \mathbb{N}$ and satisfies state and input constraints ($x_t \in X_{\mathrm{adm}}, \mu(x_t)_0 \in U_{\mathrm{adm}}$) for all $t \in \mathbb{N}$.
4. **Exact Shifted Cost Decomposition (`mpcCost_shiftInput_eq`) & Value Descent (`mpc_value_descent`)**: Under the terminal Control Lyapunov Function (CLF) condition $V_f(\mathrm{step}(x, \kappa_f(x))) + \ell(x, \kappa_f(x)) \le V_f(x)$ on $X_f$, the shifted candidate cost satisfies $J_N(x_1, u') \le J_N(x_0, u) - \ell(x_0, u_0)$.
5. **Optimal Value Function Lyapunov Decrease & Cumulative Cost Bound (`mpc_optimal_value_descent`, `mpc_closed_loop_cost_bound`)**: For an optimal MPC policy $\mu$, the optimal value function $V_N^*(x) = J_N(x, \mu(x))$ decreases by at least $\ell(x_t, \mu(x_t)_0)$ at every step, yielding the telescopic finite-horizon performance bound $\sum_{t=0}^{T-1} \ell(x_t, \mu(x_t)_0) \le V_N^*(x_0) - V_N^*(x_T)$.

All definitions and theorems are developed for arbitrary discrete-time transition systems `step : X → U → X` (encompassing both nonlinear and linear MPC) and specialized to linear time-invariant (LTI) systems $x_{k+1} = A x_k + B u_k$ (`lti_mpc_recursive_feasibility_step`).

---

## 2. Mathematical Formulation

### 2.1 Constrained Discrete-Time Prediction Dynamics
Let $X$ be the state space, $U$ be the control input space, and $\mathrm{step} : X \to U \to X$ be the discrete-time state transition map. Given an initial state $x_0 \in X$ and an open-loop input sequence $u : \mathbb{N} \to U$, the predicted state trajectory $x_k = \mathrm{mpcTraj}(\mathrm{step}, x_0, u, k)$ is defined recursively by:
$$x_0 = x_0, \qquad x_{k+1} = \mathrm{step}(x_k, u_k) \quad (k \in \mathbb{N}).$$

Two structural properties of `mpcTraj` underpin the warm-start analysis:
- **Time-Shift Invariance (`mpcTraj_shift`)**:
  $$\mathrm{mpcTraj}(\mathrm{step}, \mathrm{step}(x_0, u_0), (j \mapsto u_{j+1}), k) = \mathrm{mpcTraj}(\mathrm{step}, x_0, u, k + 1).$$
- **Causal Prefix Congruence (`mpcTraj_congr`)**:
  If $u_1(j) = u_2(j)$ for all $j < k$, then $\mathrm{mpcTraj}(\mathrm{step}, x_0, u_1, k) = \mathrm{mpcTraj}(\mathrm{step}, x_0, u_2, k)$.

### 2.2 Admissibility and Terminal Control Invariance
Let $X_{\mathrm{adm}} \subseteq X$ be the set of admissible states, $U_{\mathrm{adm}} \subseteq U$ be the set of admissible control inputs, and $X_f \subseteq X$ be the terminal constraint set.

- **Horizon-$N$ Admissibility (`IsAdmissibleHorizon`)**:
  For horizon $N \in \mathbb{N}$, an input sequence $u : \mathbb{N} \to U$ is horizon-$N$ admissible from $x_0$ if:
  $$\forall k < N,\; x_k \in X_{\mathrm{adm}}, \qquad \forall k < N,\; u_k \in U_{\mathrm{adm}}, \qquad x_N \in X_f.$$
- **Control Invariant Terminal Set (`IsControlInvariant`)**:
  The terminal set $X_f$ is control invariant under terminal feedback law $\kappa_f : X \to U$ if:
  $$X_f \subseteq X_{\mathrm{adm}}, \qquad \forall x \in X_f,\; \kappa_f(x) \in U_{\mathrm{adm}}, \qquad \forall x \in X_f,\; \mathrm{step}(x, \kappa_f(x)) \in X_f.$$

### 2.3 Warm-Start Candidate Construction and Recursive Feasibility
Suppose $u$ is horizon-$N$ admissible from $x_0$ with $N \ge 1$. After applying $u_0$, the system transitions to $x_1 = \mathrm{step}(x_0, u_0)$. We construct the shifted candidate input sequence $u' = \mathrm{shiftInput}(\mathrm{step}, \kappa_f, N, x_0, u)$ by:
$$u'(k) = \begin{cases} u(k + 1) & \text{if } k + 1 < N, \\ \kappa_f(x_N) & \text{if } k + 1 \ge N. \end{cases}$$

By causal prefix congruence and time-shift invariance (`mpcTraj_shiftInput_of_le`), for all $k$ with $k + 1 \le N$, the state trajectory $x'_k = \mathrm{mpcTraj}(\mathrm{step}, x_1, u', k)$ satisfies:
$$x'_k = x_{k+1}.$$
In particular, at $k = N - 1$, $x'_{N-1} = x_N \in X_f \subseteq X_{\mathrm{adm}}$, and at the terminal index $k = N$ (`mpcTraj_shiftInput_terminal`):
$$x'_N = \mathrm{step}(x'_{N-1}, u'(N - 1)) = \mathrm{step}(x_N, \kappa_f(x_N)) \in X_f.$$
Consequently, $u'$ satisfies all state, input, and terminal constraints over horizon $N$ from $x_1$ (`mpc_recursive_feasibility_step`). By induction on $t \in \mathbb{N}$, any receding-horizon MPC policy $\mu : X \to (\mathbb{N} \to U)$ that selects an admissible plan whenever one exists remains feasible forever and satisfies $x_t \in X_{\mathrm{adm}}$ and $\mu(x_t)_0 \in U_{\mathrm{adm}}$ for all $t \in \mathbb{N}$ (`mpc_closed_loop_feasible`).

### 2.4 Finite-Horizon Cost Decomposition and Lyapunov Descent
Given stage cost $\ell : X \to U \to \mathbb{R}$ and terminal cost $V_f : X \to \mathbb{R}$, the horizon-$N$ MPC objective is:
$$J_N(x_0, u) = \sum_{k=0}^{N-1} \ell(x_k, u_k) + V_f(x_N).$$

Evaluating $J_N(x_1, u')$ along the shifted candidate trajectory $u'$ and splitting the finite sums at $k = 0$ and $k = N - 1$ yields the exact algebraic identity (`mpcCost_shiftInput_eq`):
$$J_N(x_1, u') = J_N(x_0, u) - \ell(x_0, u_0) + \Bigl(V_f(\mathrm{step}(x_N, \kappa_f(x_N))) + \ell(x_N, \kappa_f(x_N)) - V_f(x_N)\Bigr).$$

When $V_f$ is a **terminal Control Lyapunov Function** on $X_f$ (`IsTerminalCLF`), meaning:
$$\forall x \in X_f,\quad V_f(\mathrm{step}(x, \kappa_f(x))) + \ell(x, \kappa_f(x)) \le V_f(x),$$
the terminal residual is non-positive because $x_N \in X_f$. This immediately establishes candidate cost descent (`mpc_value_descent`):
$$J_N(x_1, u') \le J_N(x_0, u) - \ell(x_0, u_0).$$
Furthermore, if $\mu$ is an optimal MPC policy (`IsOptimalMPCPolicy`), optimality at $x_1$ implies $V_N^*(x_1) = J_N(x_1, \mu(x_1)) \le J_N(x_1, u')$, yielding the fundamental MPC Lyapunov inequality (`mpc_optimal_value_descent`):
$$V_N^*(\mathrm{step}(x, \mu(x)_0)) \le V_N^*(x) - \ell(x, \mu(x)_0),$$
and by telescopic summation over $T$ closed-loop steps (`mpc_closed_loop_cost_bound`):
$$\sum_{t=0}^{T-1} \ell(x_t, \mu(x_t)_0) \le V_N^*(x_0) - V_N^*(x_T).$$

---

## 3. Formalization Architecture in Lean 4

The complete formalization is implemented in `ControlsLean/Controls/MPCFeasibility.lean`.

### 3.1 Formal Definitions
```lean
/-- Open-loop state trajectory predicted from initial state `x₀` under input sequence `u`. -/
def mpcTraj (step : X → U → X) (x₀ : X) (u : ℕ → U) : ℕ → X
  | 0 => x₀
  | k + 1 => step (mpcTraj step x₀ u k) (u k)

/-- The standard MPC warm-start shifted input sequence for horizon `N`. -/
def shiftInput (step : X → U → X) (κ_f : X → U) (N : ℕ) (x₀ : X) (u : ℕ → U) (k : ℕ) : U :=
  if k + 1 < N then u (k + 1) else κ_f (mpcTraj step x₀ u N)

/-- Control invariant terminal constraint set `X_f` under terminal control law `κ_f`. -/
structure IsControlInvariant (step : X → U → X) (X_adm : Set X) (U_adm : Set U)
    (X_f : Set X) (κ_f : X → U) : Prop where
  subset_adm : X_f ⊆ X_adm
  input_adm : ∀ x ∈ X_f, κ_f x ∈ U_adm
  step_mem : ∀ x ∈ X_f, step x (κ_f x) ∈ X_f

/-- Horizon-`N` admissible open-loop trajectory from `x₀`. -/
structure IsAdmissibleHorizon (step : X → U → X) (X_adm : Set X) (U_adm : Set U)
    (X_f : Set X) (N : ℕ) (x₀ : X) (u : ℕ → U) : Prop where
  state_adm : ∀ k < N, mpcTraj step x₀ u k ∈ X_adm
  input_adm : ∀ k < N, u k ∈ U_adm
  terminal_mem : mpcTraj step x₀ u N ∈ X_f

/-- Finite-horizon MPC cost functional `J_N(x₀, u)`. -/
def mpcCost (step : X → U → X) (ℓ : X → U → ℝ) (V_f : X → ℝ)
    (N : ℕ) (x₀ : X) (u : ℕ → U) : ℝ :=
  (∑ k ∈ Finset.range N, ℓ (mpcTraj step x₀ u k) (u k)) + V_f (mpcTraj step x₀ u N)

/-- Terminal Control Lyapunov Function (CLF) condition on `X_f`. -/
def IsTerminalCLF (step : X → U → X) (ℓ : X → U → ℝ) (V_f : X → ℝ)
    (X_f : Set X) (κ_f : X → U) : Prop :=
  ∀ x ∈ X_f, V_f (step x (κ_f x)) + ℓ x (κ_f x) ≤ V_f x
```

### 3.2 Headline Theorems
```lean
/-- **Headline Theorem 1 — One-Step MPC Recursive Feasibility**: -/
theorem mpc_recursive_feasibility_step {step : X → U → X} {X_adm : Set X} {U_adm : Set U}
    {X_f : Set X} {κ_f : X → U} {N : ℕ} (hN : 0 < N)
    (hinv : IsControlInvariant step X_adm U_adm X_f κ_f)
    {x₀ : X} {u : ℕ → U}
    (hu : IsAdmissibleHorizon step X_adm U_adm X_f N x₀ u) :
    IsAdmissibleHorizon step X_adm U_adm X_f N
      (step x₀ (u 0)) (shiftInput step κ_f N x₀ u)

/-- **Headline Theorem 2 — Eternal Closed-Loop MPC Feasibility**: -/
theorem mpc_closed_loop_feasible {step : X → U → X} {X_adm : Set X} {U_adm : Set U}
    {X_f : Set X} {κ_f : X → U} {N : ℕ} (hN : 0 < N)
    (hinv : IsControlInvariant step X_adm U_adm X_f κ_f)
    {μ : X → (ℕ → U)} (hμ : IsAdmissibleMPCPolicy step X_adm U_adm X_f N μ)
    {x₀ : X} (hx₀ : IsFeasibleState step X_adm U_adm X_f N x₀) (t : ℕ) :
    IsFeasibleState step X_adm U_adm X_f N (mpcClosedLoopTraj step μ x₀ t) ∧
      mpcClosedLoopTraj step μ x₀ t ∈ X_adm ∧
      μ (mpcClosedLoopTraj step μ x₀ t) 0 ∈ U_adm

/-- **Headline Theorem 3 — MPC Value Function Lyapunov Descent**: -/
theorem mpc_value_descent {step : X → U → X} {X_adm : Set X} {U_adm : Set U}
    {X_f : Set X} {κ_f : X → U} {ℓ : X → U → ℝ} {V_f : X → ℝ}
    {N : ℕ} (hN : 0 < N)
    (hclf : IsTerminalCLF step ℓ V_f X_f κ_f)
    {x₀ : X} {u : ℕ → U}
    (hu : IsAdmissibleHorizon step X_adm U_adm X_f N x₀ u) :
    mpcCost step ℓ V_f N (step x₀ (u 0)) (shiftInput step κ_f N x₀ u) ≤
      mpcCost step ℓ V_f N x₀ u - ℓ x₀ (u 0)

/-- **Optimal Value Function One-Step Lyapunov Decrease**: -/
theorem mpc_optimal_value_descent {step : X → U → X} {X_adm : Set X} {U_adm : Set U}
    {X_f : Set X} {κ_f : X → U} {ℓ : X → U → ℝ} {V_f : X → ℝ}
    {N : ℕ} (hN : 0 < N)
    (hinv : IsControlInvariant step X_adm U_adm X_f κ_f)
    (hclf : IsTerminalCLF step ℓ V_f X_f κ_f)
    {μ : X → (ℕ → U)} (hopt : IsOptimalMPCPolicy step X_adm U_adm X_f ℓ V_f N μ)
    {x : X} (hx : IsFeasibleState step X_adm U_adm X_f N x) :
    mpcCost step ℓ V_f N (step x (μ x 0)) (μ (step x (μ x 0))) ≤
      mpcCost step ℓ V_f N x (μ x) - ℓ x (μ x 0)
```

---

## 4. Novelty Analysis & Gap Positioning

### 4.1 Comparison against Seed Codebase (`ControlsLean.Controls`)
- **Seed Baseline**: `ControlsLean.Controls.DiscreteLyapunov` formalizes unconstrained autonomous discrete-time stability ($x_{k+1} = A x_k$) via quadratic Lyapunov functions, and `ControlsLean.Controls.Reachability` / `Gramian` formalize unconstrained finite-horizon steering.
- **Novelty of `MPCFeasibility.lean`**: Introduces hard pointwise state constraints ($x_k \in X_{\mathrm{adm}}$), hard input constraints ($u_k \in U_{\mathrm{adm}}$), terminal control invariance ($X_f, \kappa_f$), receding-horizon warm-start shifting, eternal closed-loop constraint satisfaction, and optimal value function Lyapunov decrease.

### 4.2 Comparison against Mathlib and `LeanForControl`
- Neither Mathlib nor `LeanForControl` contains any formalization of Model Predictive Control, receding-horizon control, control invariant terminal sets, or MPC value function descent.

---

## 5. Literature Grounding & Citations

1. **Rawlings, J. B., Mayne, D. Q., & Diehl, M.** (2017). *Model Predictive Control: Theory, Computation, and Design* (2nd ed.). Nob Hill Publishing, Madison, WI.
   - *Significance*: Chapter 2, Sections 2.4–2.5 (Assumptions 2.2–2.3 and Theorem 2.19) establish recursive feasibility and Lyapunov cost decrease via control invariant terminal sets and terminal Control Lyapunov Functions.
2. **Mayne, D. Q., Rawlings, J. B., Rao, C. V., & Scokaert, P. O. M.** (2000). "Constrained model predictive control: Stability and optimality." *Automatica*, 36(6): 789–814.
   - *Significance*: Unifying survey proving that the triplet $(X_f, \kappa_f, V_f)$ guarantees recursive feasibility and asymptotic stability across constrained MPC formulations.
3. **Keerthi, S. S., & Gilbert, E. G.** (1988). "Optimal infinite-horizon feedback laws for a general class of constrained discrete-time systems: Stability and moving-horizon approximations." *Journal of Optimization Theory and Applications*, 57(2): 265–293.

---

## 6. Verification and Machine-Checked Proof Audit

- **Single-File Verification Command**:
  ```bash
  export PATH="$HOME/.elan/bin:$PATH" && lake env lean ControlsLean/Controls/MPCFeasibility.lean
  ```
- **Axiomatic Footprint**:
  - `mpc_recursive_feasibility_step`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
  - `mpc_closed_loop_feasible`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
  - `mpcCost_shiftInput_eq`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
  - `mpc_value_descent`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
  - `mpc_optimal_value_descent`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
  - `mpc_closed_loop_cost_bound`: depends exclusively on `[propext, Classical.choice, Quot.sound]`
- **Zero Escape Hatches**: Zero `sorry`, zero `admit`, zero custom `axiom`s.
