# Lean 4 Proof Engineering Playbook for Controls & Applied Math

A practical guide for engineers, researchers, and AI agents authoring machine-checked proofs in `ctrl`.

---

## 1. Golden Architectural Principles

### 1. Representation Tiering: Don't Default to Coordinates
- **Abstract Ring Operators** (`InformationFilter.lean`): For algebraic matrix identities (e.g. Sherman–Morrison–Woodbury, parallel sum, matrix inversion lemmas), state theorems over an arbitrary associative `[Ring α]`. Avoid concrete `Matrix (Fin n) (Fin n) ℝ` until required. Ring identities typecheck faster and have 0 index overhead.
- **Coordinate-Free Submodules** (`Reachability.lean`): For qualitative properties (reachability, observability, invariant subspaces), use `Submodule K V` and `LinearMap`. Avoid Cayley–Hamilton and polynomial rings when dimension counting (`finrank K V`) and monotonic chain stationarity suffice.
- **Topological Compactness over Spectral Theorems** (`DiscreteLyapunov.lean`): Mathlib's `Matrix.PosDef` enforces conjugate symmetry (`M = Mᵀ`). In control theory, asymmetric matrices often satisfy $x^\top M x > 0$. Use `quad M x = x ⬝ᵥ (M *ᵥ x)` and compactness of the Euclidean unit sphere (`Metric.isCompact_sphere`) with Extreme Value Theorem (`ContinuousOn.exists_isMinOn`) to establish sharp quadratic bounds $c \|x\|^2 \le x^\top M x \le C \|x\|^2$ without requiring $M = M^\top$.
- **Explicit Canonical Coordinates for Synthesis** (`PolePlacement.lean`): Use explicit `Fin 2` or `Fin n` coordinates only when synthesizing specific controllers (companion matrices, deadbeat gains, observer feedback).

---

## 2. Common Proof Patterns & Tactic Idioms

### Matrix & Quadratic Form Manipulation
Always use `ControlsLean.Tactics`:
```lean
import ControlsLean.Tactics.ControlTactics

-- 1. Invariance under transposition:
quad Mᵀ x = quad M x              -- quad_transpose

-- 2. Vanishing of skew-symmetric components:
Mᵀ = -M → quad M x = 0            -- quad_skew

-- 3. Decoupled block forms:
quad (fromBlocks A 0 0 D) [u; v] = quad A u + quad D v   -- quad_fromBlocks_diag

-- 4. Connection to Mathlib PosDef:
Matrix.PosDef M ↔ Mᵀ = M ∧ ∀ x ≠ 0, 0 < quad M x         -- posDef_iff_quad_pos
```

### Linear Fractional Transformations & Riccati Iterates
When working with Riccati equations $P_{k+1} = \frac{P_k R}{P_k + R} + Q$:
1. **Parallel Sum Form**: Notice $\frac{P R}{P + R} = (P^{-1} + R^{-1})^{-1}$. Use `inv_parallel_sum` to convert into precision space.
2. **Contraction Step**: The difference of two Riccati iterates satisfies:
   $$\left(\frac{P_1 R}{P_1 + R} + Q\right) - \left(\frac{P_2 R}{P_2 + R} + Q\right) = \frac{R^2 (P_1 - P_2)}{(P_1 + R)(P_2 + R)}$$
   Use `riccati_lft_sub` and bound the denominator using iterate lower bounds $P_k \ge Q > 0$.
3. **Clearing Denominators**: Use `field_simp; ring` to prove algebraic equalities of rational functions, then finish bounds with `positivity` or `gcongr`.

### Discrete Lyapunov Stability Chaining
Avoid manual induction on time steps $k$:
```lean
-- Map iteration: V (A x) ≤ ρ * V x  ==>  V (A^k x₀) ≤ ρ^k * V x₀
apply quad_lyapunov_geometric h_contract k
```

---

## 3. High-Frequency Gotchas & Fixes

| Gotcha | Problem | Solution |
|---|---|---|
| **Operator Precedence** | `A ^ i ∘ₗ B` parses as `A ^ (i ∘ₗ B)` | Always write `(A ^ i) ∘ₗ B` |
| **Namespace Collision** | `range` can mean `Set.range` | Add `open LinearMap (range)` |
| **Negation Pushing** | `push_neg` is deprecated | Use `push Not` |
| **Sum Reversal** | Reversing $\sum_{i=0}^{k-1} f(i)$ to $f(k-1-i)$ | Use `Fin.revPerm` and `Equiv.sum_comp` (see `Gramian.lean`) |
| **PosDef Finsupp** | `Matrix.PosDef` is phrased via `Finsupp` | Use `posDef_iff_dotProduct_mulVec` or `posDef_iff_quad_pos` |
| **Nonlinear Inequalities** | `nlinarith` times out or fails silently | Factor out sub-expressions with `have`, prove sign with `positivity`, then feed to `linarith` |

---

## 4. Inner Loop Developer Tools (`./ctrl`)

Always use the `./ctrl` CLI for development:
- **Fast file verification**: `./ctrl check ControlsLean/Path/File.lean`
- **Sub-second scratch testing**: `./ctrl scratch -c "example : 1 + 1 = 2 := by rfl"`
- **Semantic lemma lookup**: `./ctrl search "Matrix.PosDef"` or `./ctrl search "(x : ℝ) : 0 < Real.exp x"`
- **Bounty filter**: `./ctrl triage candidates.json` (screens 300 candidates in 0.2s)
- **Axiom verification**: `./ctrl audit`
