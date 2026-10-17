# Architectural Design Principles and Verification Discipline of `ctrl`

**Author**: `ctrl` Documentation & Architecture Team  
**Date**: October 2026  
**Repository**: `https://github.com/IamMikeHelsel/ctrl`  
**Toolchain**: Lean 4 `v4.36.0-rc1` (Mathlib rev `625d8914`)

---

## 1. Architectural Philosophy

The `ctrl` library is engineered to bridge the profound gap between theoretical control engineering, robotic perception, state estimation, and machine-checked interactive theorem proving in Lean 4.

Historically, formalization efforts in theorem provers suffer from two common failure modes:
1. **The Over-Generalization Trap**: Formulating every definition at the highest possible category-theoretic abstraction (e.g. general topoi, infinite-dimensional operator algebras) before elementary, computable engineering theorems can even be stated.
2. **The Coordinate Hell Trap**: Formulating everything in concrete $n \times m$ matrix indices from line one, leading to combinatorial explosion in index arithmetic, difficult proofs of matrix associativity, and dependent type friction with dimensions ($n + m$, $\mathrm{Fin}\ k$).

`ctrl` resolves this tension by adhering to four pragmatic architectural maxims:
- **Minimal Overhead, Maximal Clarity**: Write definitions that immediately yield clear mathematical insight and lean, performant proofs.
- **Appropriate Representation Tiering**: Use coordinate-free linear maps for structural invariance and stationarity; use concrete `Fin n` coordinates for geometric/estimation algorithms; use abstract rings for algebraic operator identities.
- **Elimination of Artificial Constraints**: Strip away mathematical restrictions (such as matrix symmetry in Lyapunov functions) that do not serve the core dynamical conclusions.
- **Uncompromising Axiom Discipline**: Restrict all proofs to standard foundational Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`), continuously enforced by automated CI auditing.

---

## 2. Core Design Principles

### 2.1 Principle 1: Eliminating Unnecessary Matrix Symmetry Constraints

#### The Problem with Mathlib's `Matrix.PosDef`
In classical textbook presentations, discrete Lyapunov stability is often stated for symmetric matrices:
$$V(x) = x^\top P x, \qquad P = P^\top \succ 0, \qquad P - A^\top P A \succ 0.$$
Mathlib mirrors this in `Mathlib.LinearAlgebra.Matrix.PosDef`, which explicitly enforces conjugate symmetry:
```lean
def PosDef (M : Matrix n n R) : Prop :=
  M.IsHermitian ∧ ∀ x : n → R, x ≠ 0 → 0 < dotProduct (star x) (M *ᵥ x)
```
However, in many real-world systems—such as asymmetric network consensus dynamics, non-normal hydrodynamic operators, and state feedback matrices—one frequently encounters matrices $P$ where $x^\top P x > 0$ for all $x \ne 0$, yet $P \ne P^\top$. Forcing the formalizer to symmetrize $P_{\text{sym}} = \frac{1}{2}(P + P^\top)$ before applying stability theorems creates unnecessary algebraic friction.

#### The `ctrl` Asymmetric Geometric Approach
In `ControlsLean/Controls/DiscreteLyapunov.lean`, we define quadratic forms directly:
```lean
def quad (M : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  x ⬝ᵥ (M *ᵥ x)
```
Rather than relying on spectral decompositions of symmetric matrices, we exploit the topological compactness of the Euclidean unit sphere in $\mathbb{R}^n$:
$$\mathbb{S}^{n-1} = \{ x \in \mathbb{R}^n \mid \|x\| = 1 \}.$$
Because the unit sphere is compact (`Metric.isCompact_sphere`) and non-empty, and the quadratic form $x \mapsto x^\top M x$ is continuous (`continuous_quad`), the Extreme Value Theorem (`ContinuousOn.exists_isMinOn`) guarantees the existence of a strictly positive lower bound:
$$c = \min_{x \in \mathbb{S}^{n-1}} x^\top M x > 0.$$
By homogeneity ($x = \|x\| u$ for $u \in \mathbb{S}^{n-1}$), this immediately establishes the sharp quadratic envelope:
$$c \|x\|^2 \le x^\top M x \le C \|x\|^2, \qquad \forall x \in \mathbb{R}^n.$$

Applying this to the Lyapunov difference $x^\top (P - A^\top P A) x \ge c_Q \|x\|^2$, we deduce the geometric contraction factor:
$$V(A x) \le \rho V(x), \qquad \rho = \max\left(1 - \frac{c_Q}{C_P}, 0\right) < 1.$$
Iterating $k$ times yields $V(A^k x_0) \le \rho^k V(x_0) \to 0$, which implies $A^k x_0 \to 0$ for **any** matrix $P$ satisfying the Lyapunov inequality, without requiring $P = P^\top$:
```lean
theorem tendsto_pow_mulVec_zero (A P : Matrix n n ℝ)
    (hP : ∀ x, x ≠ 0 → 0 < quad P x)
    (hQ : ∀ x, x ≠ 0 → 0 < quad (P - Aᵀ * P * A) x)
    (x₀ : n → ℝ) :
    Filter.Tendsto (fun k : ℕ => (A ^ k) *ᵥ x₀) Filter.atTop (nhds 0)
```
For users who already possess a Mathlib `Matrix.PosDef` hypothesis, `ctrl` provides a one-line corollary interface: `PosDef.tendsto_pow_mulVec_zero`.

---

### 2.2 Principle 2: Dimension Counting vs. Cayley–Hamilton for Reachability

#### The Cayley–Hamilton Friction
In classical linear control, the reachability of a discrete-time pair $(A, B)$ is defined by the range of the controllability matrix:
$$\mathcal{C}_k = [B \quad AB \quad A^2 B \quad \dots \quad A^{k-1} B].$$
To prove that the reachable subspace stops expanding after $n = \dim(V)$ steps ($\mathcal{R}_k = \mathcal{R}_n$ for all $k \ge n$), textbooks and libraries like `LeanForControl` rely on the Cayley–Hamilton theorem:
$$A^n = -\sum_{i=0}^{n-1} c_i A^i \implies A^k \in \operatorname{span}\{I, A, \dots, A^{n-1}\} \quad \forall k \ge n.$$
While mathematically valid, formalizing this requires:
1. Characteristic polynomial definitions $\det(tI - A)$.
2. Polynomial ring evaluations (`aeval_self_charpoly`).
3. Characteristic-zero and commutative ring assumptions.
4. Heavy algebraic lemmas connecting polynomial powers with matrix products.

#### The `ctrl` Dimension Counting Approach
In `ControlsLean/Controls/Reachability.lean`, we formulate reachability coordinate-free over an arbitrary field $K$ using a recursive submodule:
```lean
def reach (A : V →ₗ[K] V) (B : U →ₗ[K] V) : ℕ → Submodule K V
  | 0 => ⊥
  | k + 1 => LinearMap.range B ⊔ (reach A B k).map A
```
This construction exhibits natural monotonicity:
$$R_0 \le R_1 \le R_2 \le \dots \le R_k \le R_{k+1}.$$
We prove two purely structural lemmas:
1. **Stationarity Propagation (`reach_stable`)**: If $R_m = R_{m+1}$, then $R_k = R_m$ for all $k \ge m$.
2. **Strict Growth or Equal (`le_finrank_reach`)**: If the chain grows strictly at every step ($R_i < R_{i+1}$ for all $i < k$), then:
   $$\dim(R_k) \ge k.$$

Since $V$ has finite dimension $n = \mathrm{finrank}(K, V)$, the dimension cannot exceed $n$. By the pigeonhole principle on finite dimensions, the chain **must** become stationary at some step $m \le n$:
```lean
theorem reach_eq_reach_finrank (A : V →ₗ[K] V) (B : U →ₗ[K] V) (k : ℕ)
    (hk : finrank K V ≤ k) :
    reach A B k = reach A B (finrank K V)
```
**Benefits of Dimension Counting**:
- Proved in only 25 lines of Lean 4.
- Holds over **any field $K$** (including finite fields $\mathbb{F}_p$, where Cayley–Hamilton is awkward).
- Requires zero polynomial or determinant machinery.
- Directly enables feedback invariance `reach(A + B ∘ₗ F, B, k) = reach(A, B, k)` by simple submodule induction.

---

### 2.3 Principle 3: Multi-Tier State Representations

To prevent impedance mismatch between mathematical concepts and Lean 4 types, `ctrl` uses three distinct representation tiers:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          Tier 1: Coordinate-Free                            │
│  Types: V →ₗ[K] V,  Submodule K V                                           │
│  Scope: Structural invariance, reachability chains, feedback submodules     │
└──────────────────────────────────────┬──────────────────────────────────────┘
                                       │
┌──────────────────────────────────────┴──────────────────────────────────────┐
│                        Tier 2: Generic Matrix Rings                         │
│  Types: Matrix n n ℝ with [Fintype n], associative Ring α                   │
│  Scope: Energy Gramians, Lyapunov decay, Sherman–Morrison–Woodbury          │
└──────────────────────────────────────┬──────────────────────────────────────┘
                                       │
┌──────────────────────────────────────┴──────────────────────────────────────┐
│                    Tier 3: Concrete Fin n Coordinates                       │
│  Types: Matrix (Fin 3) (Fin 3) K,  Fin 2 companion forms                   │
│  Scope: Epipolar geometry, planar homography collineations, deadbeat control│
└─────────────────────────────────────────────────────────────────────────────┘
```

1. **Tier 1 (Coordinate-Free)**:
   Used in `ControlsLean/Controls/Reachability.lean`. By working with `Submodule K V`, proofs avoid matrix indices, transposes, and dimension arithmetic.
2. **Tier 2 (Generic Matrix & Operator Rings)**:
   Used in `ControlsLean/Controls/Gramian.lean` and `ControlsLean/Estimation/InformationFilter.lean`.
   For the Sherman–Morrison–Woodbury theorem, rather than burdening the proof with 4-way block matrix indices, we prove the identity for an arbitrary associative ring `α`:
   ```lean
   theorem woodbury_right_inv (A A_inv C C_inv U V M M_inv : α)
       (hA : A * A_inv = 1) (hC : C * C_inv = 1)
       (hM_def : M = C_inv + V * A_inv * U)
       (hM : M * M_inv = 1) :
       (A + U * C * V) * (A_inv - A_inv * U * M_inv * V * A_inv) = 1
   ```
   This is immediately instantiable to $n \times n$ matrices, bounded Hilbert space operators, or rational transfer function matrices.
3. **Tier 3 (Concrete Coordinates for Vision and Canonical Forms)**:
   In computer vision (`Vision/Epipolar.lean`, `Vision/Homography.lean`), physical cameras operate in 3D projective space $\mathbb{P}^2$. Formulating these in `Matrix (Fin 3) (Fin 3) K` matches the standard robotics literature (Hartley & Zisserman) and allows direct automated computation via `fin_cases`, `det_fin_three`, and `ring`.

---

### 2.4 Principle 4: Characteristic-Free Formulations

Wherever feasible, geometric and algebraic theorems are stated over an arbitrary field `K`:
- `ControlsLean/Vision/Epipolar.lean`: Calibrated epipolar constraints and cross product matrix properties $[t]_\times$ are proved over `Field K` (not restricted to $\mathbb{R}$).
- `ControlsLean/Vision/Homography.lean`: Planar collineation, line transformation duality $l' = H^{-\top} l$, and collinearity preservation are proved over `Field K`.
- `ControlsLean/Controls/PolePlacement.lean`: 2D companion controllable form, feedback gain matching, and deadbeat degree-2 nilpotence are proved over `Field K`.

This generality ensures that results can be applied not only to classical continuous control ($\mathbb{R}$) and complex frequency domains ($\mathbb{C}$), but also to finite fields ($\mathbb{F}_q$) in coding theory and digital cryptography.

---

## 3. Axiom Discipline & Foundational Integrity

### 3.1 Strict Axiom Policy
The integrity of a formal mathematics library depends entirely on its foundational consistency. The Lean 4 kernel permits user-defined axioms via the `axiom` keyword. Careless use of custom axioms can easily introduce logical inconsistency (proving `False`) or reduce proofs to trivial tautologies.

**The `ctrl` Axiom Policy**:
1. **Zero Custom Axioms**: No file in the repository may introduce a custom `axiom` declaration.
2. **Zero Incomplete Proofs**: No `sorry` or `admit` placeholders are permitted in any production module.
3. **Foundational Standard Axioms Only**: Every public headline theorem must depend strictly on the standard core axioms of Lean 4:
   - `propext` (Propositional Extensionality)
   - `Classical.choice` (Axiom of Choice)
   - `Quot.sound` (Quotient Soundness)

### 3.2 Programmatic Axiom Auditing
To enforce this policy automatically, the repository includes `scripts/Audit.lean`. This script executes `#print axioms <decl>` on all headline theorems.

Example snippet from `scripts/Audit.lean`:
```lean
#print axioms ControlsLean.Vision.epipolar_constraint
#print axioms ControlsLean.Vision.det_essential
#print axioms ControlsLean.Vision.det_homography_three_points
#print axioms ControlsLean.Vision.plane_homography_constraint
#print axioms ControlsLean.Controls.isHurwitz2_iff
#print axioms ControlsLean.Controls.reach_eq_reach_finrank
#print axioms ControlsLean.Controls.controllable_feedback
#print axioms ControlsLean.Controls.gramian_steer
#print axioms ControlsLean.Controls.deadbeat_trajectory_zero
#print axioms ControlsLean.Controls.tendsto_pow_mulVec_zero
#print axioms ControlsLean.Estimation.inv_postVarOpt
#print axioms ControlsLean.Estimation.kalman_postVar_information_equiv
#print axioms ControlsLean.Estimation.riccati_fixed_unique
```

When verified, Lean 4 outputs:
```text
'ControlsLean.Vision.epipolar_constraint' depends on axioms: [propext, Classical.choice, Quot.sound]
'ControlsLean.Vision.plane_homography_constraint' depends on axioms: [propext, Classical.choice, Quot.sound]
'ControlsLean.Controls.gramian_steer' depends on axioms: [propext, Classical.choice, Quot.sound]
'ControlsLean.Estimation.kalman_postVar_information_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'ControlsLean.Controls.deadbeat_trajectory_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Any theorem depending on non-standard axioms or unproven hypotheses immediately fails CI.

---

## 4. Automated Continuous Verification Pipeline

The repository provides a fast, reproducible verification toolchain:

### 4.1 Verification via `scripts/check.sh`
`scripts/check.sh` is the single source of truth for repository health. It operates in two modes:

1. **Full Verification Mode (`bash scripts/check.sh`)**:
   - Executes `lake build` to compile the entire library.
   - Greps every `.lean` file under `ControlsLean/` for forbidden tokens:
     ```bash
     grep -En "(sorry|admit)" ...
     grep -En "^[[:space:]]*axiom[[:space:]]" ...
     ```
   - Executes `lake env lean scripts/Audit.lean` and verifies that every output line strictly matches:
     `^'.*' depends on axioms: \[propext, Classical.choice, Quot.sound\]$`
   - Counts and prints the number of certified headline theorems.
2. **Single-File Rapid Mode (`bash scripts/check.sh <file.lean>`)**:
   - Executes `lake env lean <file.lean>`.
   - Checks the specific file for `sorry`, `admit`, and custom `axiom`.
   - Completes in ~1.5 to 2.5 seconds, enabling instantaneous feedback during theorem authoring.

### 4.2 Build Cache Strategy: Symbolic Link Architecture
Mathlib comprises over 6.1 GB of precompiled `.olean` object files in `.lake/packages/mathlib/.lake/build/lib`. Compiling Mathlib from scratch requires 1.5 to 3 hours of CPU time.

To achieve immediate builds without duplicating 7 GB on disk:
- `ctrl` symlinks the `.lake` build cache from `/Users/mike/lean-work/ControlsLean/.lake`:
  ```bash
  ln -s /Users/mike/lean-work/ControlsLean/.lake /Users/mike/lean-work/ctrl/.lake
  ```
- **The Git Symlink Gotcha**: In Git, directory entries with trailing slashes (e.g. `.lake/`) match real directories but **fail** to match symbolic links (Git mode 120000). To prevent `.lake` from being tracked as an untracked file or dirtying git status, `.gitignore` specifies `.lake` both with and without trailing slashes:
  ```gitignore
  .lake
  .lake/
  /.lake
  /.lake/
  ```
This architecture achieves **1.2-second full library re-checks** and zero disk duplication.

---

## 5. Repository Layout and Conventions

The codebase is organized into clean functional namespaces:

```text
/Users/mike/lean-work/ctrl/
├── ControlsLean.lean           Master root library import
├── ControlsLean/
│   ├── Vision/                 Computer vision and projective geometry
│   │   ├── Epipolar.lean       Essential matrix, epipolar lines, cross products
│   │   └── Homography.lean     Planar homography, line duality, collinearity
│   ├── Controls/               Control theory, stability, and synthesis
│   │   ├── Hurwitz2.lean       Second-order polynomial Hurwitz stability
│   │   ├── Reachability.lean   Submodule reachability without Cayley–Hamilton
│   │   ├── Gramian.lean        Controllability Gramian and minimum-energy steering
│   │   ├── PolePlacement.lean  Ackermann companion placement and deadbeat control
│   │   └── DiscreteLyapunov.lean Asymmetric Lyapunov stability via sphere compactness
│   └── Estimation/             State estimation and filtering
│       ├── ScalarKalman.lean   Scalar Kalman filter optimality and Riccati dynamics
│       └── InformationFilter.lean Sherman–Morrison–Woodbury and Information filter
├── docs/                       Architecture, landscape, roadmap, and proposals
│   ├── landscape.md            Three-way comparative ecosystem analysis
│   ├── architecture.md         This design document
│   ├── roadmap.md              Prioritized development plan and bounty triage
│   ├── README.md               Documentation index
│   └── proposals/              Detailed research proposals for new additions
├── scripts/
│   ├── check.sh                Continuous automated verification script
│   ├── Audit.lean              Programmatic headline axiom auditor
│   ├── sync.sh                 Google Drive cloud backup script
│   └── bounty_triage.sh        Erdős / formal mathematics bounty triage utility
├── lakefile.toml               Lake project manifest
├── lake-manifest.json          Pinned dependency lockfile
├── lean-toolchain              Toolchain specification (v4.36.0-rc1)
├── AGENTS.md                   Agent rules and Lean 4 coding gotchas
└── BOUNTIES.md                 Bounty program guide and prize pipeline
```

---

## 6. Summary of Design Decisions

| Challenge | Traditional Approach | `ctrl` Solution |
|---|---|---|
| Matrix Symmetry | Impose $P = P^\top$ via `Matrix.PosDef` | Asymmetric quadratic forms via unit sphere compactness |
| Reachability Stationarity | Cayley–Hamilton polynomial expansion | Finite dimension counting on ascending submodule chains |
| State Representation | Monolithic concrete matrices | 3-Tier: Coordinate-free, generic rings, concrete `Fin n` |
| Field Dependence | Restrict to $\mathbb{R}$ or $\mathbb{C}$ | Field-agnostic `Field K` where algebraically possible |
| Operator Inversion | 4-way block matrix indices | Ring-general Sherman–Morrison–Woodbury identity |
| Axiom Verification | Manual spot-checks | Automated CI `#print axioms` scanner in `scripts/check.sh` |
| Mathlib Compilation | Rebuild or duplicate 7.2 GB cache | Zero-overhead `.lake` symlink with git-symlink hygiene |
