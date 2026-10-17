# `ctrl` Documentation Index

Welcome to the documentation suite of **`ctrl`** (`https://github.com/IamMikeHelsel/ctrl`), the Lean 4 library for formal control theory, robotic state estimation, and projective computer vision.

This directory contains the foundational design documentation, comparative surveys, research roadmaps, and technical proposals for all machine-checked additions to the library.

---

## 1. Core Architectural & Landscape Documents

| Document | Title & Description | Key Focus Areas |
|---|---|---|
| **[`landscape.md`](landscape.md)** | **Comparative Landscape of Formal Control Theory** | Three-way survey comparing `ctrl` / `ControlsLean`, `LeanForControl` (67 modules, Hespanha & Khalil), and upstream `Mathlib`. Detailed side-by-side capability matrix, toolchain divergence analysis, and catalog of formalization voids. |
| **[`architecture.md`](architecture.md)** | **Architectural Design Principles & Verification Discipline** | Core design maxims: avoiding artificial matrix symmetry in Lyapunov functions, finite dimension counting vs Cayley–Hamilton, 3-tier representation strategy (coordinate-free, generic rings, `Fin n`), and strict standard axiom discipline. |
| **[`roadmap.md`](roadmap.md)** | **Prioritized Roadmap & Bounty Triage** | Near-term delivered additions, medium-term milestones (observers, Separation Principle, DARE, Kalman–Bucy, 8-point algorithm), long-term frontiers (MPC, backstepping, POMDPs), and systematic formal mathematics bounty triage pipeline. |

---

## 2. Technical Research Proposals (`docs/proposals/`)

Each proposal provides complete mathematical formulations, design rationales, novelty analyses relative to prior art, and verifiable literature citations for machine-checked modules in `ControlsLean`:

1. **[`docs/proposals/01_planar_homography.md`](proposals/01_planar_homography.md)**:  
   *Machine-Checked Planar Homography, Collineation Duality, and Plane-Induced Two-View Geometry in Lean 4.*  
   Formalizes projective collineations $H \in \mathrm{GL}(3, K)$, dual line transformations $l' = H^{-\top} l$, collinearity preservation under determinant scaling, and 3D plane-induced homographies $H = R + \frac{1}{d} t n^\top$.  
   *Target module*: `ControlsLean/Vision/Homography.lean`.  
   *Citations*: Hartley & Zisserman (2004), Faugeras & Luong (2001).

2. **[`docs/proposals/02_controllability_gramian.md`](proposals/02_controllability_gramian.md)**:  
   *The Discrete-Time Controllability Gramian and Minimum-Energy State Steering in Lean 4.*  
   Formalizes the quantitative Controllability Gramian $W_k = \sum_{i=0}^{k-1} A^i B B^\top (A^i)^\top$, unconditional symmetry $W_k^\top = W_k$, quadratic energy forms, and the exact minimum-energy steering formula $u_i = B^\top (A^\top)^{k-1-i} W_k^{-1} x_1$.  
   *Target module*: `ControlsLean/Controls/Gramian.lean`.  
   *Citations*: Kalman, Ho, & Narendra (1963), Hespanha (2018), Brockett (1970).

3. **[`docs/proposals/03_information_filter.md`](proposals/03_information_filter.md)**:  
   *Multi-Dimensional Information Filtering and the Sherman–Morrison–Woodbury Identity in Associative Rings.*  
   Formalizes the ring-general Sherman–Morrison–Woodbury matrix inversion lemma and proves the exact two-sided inverse equivalence between the Kalman covariance update $P^+$ and the Information matrix update $Y^+ = Y + C^\top R^{-1} C$.  
   *Target module*: `ControlsLean/Estimation/InformationFilter.lean`.  
   *Citations*: Woodbury (1950), Sherman & Morrison (1950), Anderson & Moore (1979), Kailath et al. (2000).

4. **[`docs/proposals/04_pole_placement_deadbeat.md`](proposals/04_pole_placement_deadbeat.md)**:  
   *State-Feedback Pole Placement and Deadbeat Control for Canonical Second-Order Systems in Lean 4.*  
   Formalizes active feedback synthesis in controllable companion canonical forms, deadbeat gain selection leading to degree-2 nilpotence $(A - B K_{db})^2 = 0$, exact 2-step state trajectory extinction, and continuous-time Hurwitz stabilization.  
   *Target module*: `ControlsLean/Controls/PolePlacement.lean`.  
   *Citations*: Ackermann (1972), Åström & Murray (2021), Franklin, Powell, & Workman (1998).

---

## 3. Verification & Continuous Auditing Guide

The `ctrl` repository enforces strict programmatic verification on every commit:

### 3.1 Running the Verification Pipeline
From the root of the repository (`/Users/mike/lean-work/ctrl`):

```bash
# Verify the entire library (builds all modules, checks for sorry/admit/axioms, audits headline theorems)
bash scripts/check.sh

# Verify a single module in rapid mode (~1.5 to 2.5s)
bash scripts/check.sh ControlsLean/Vision/Homography.lean
```

### 3.2 Programmatic Axiom Audit (`scripts/Audit.lean`)
`scripts/Audit.lean` imports the entire library and executes `#print axioms` on every headline theorem. All public results must depend **strictly** on:
```text
[propext, Classical.choice, Quot.sound]
```
Any custom `axiom`, `sorry`, or unproven lemma results in immediate build rejection.

### 3.3 Build Cache Strategy & Symlink Hygiene
To ensure fast builds (~1.2s per build replay) without duplicating the 7.2 GB Mathlib cache:
- The build directory `.lake` is symlinked to `/Users/mike/lean-work/ControlsLean/.lake`.
- The repository's `.gitignore` contains both `.lake` and `/.lake` (without trailing slashes) to prevent Git from treating the symlink as an untracked file (Git mode 120000).

---

## 4. Root Repository References

- **[`../README.md`](../README.md)**: General project overview, quickstart instructions, and module directory.
- **[`../PROJECT.md`](../PROJECT.md)**: High-level project specifications, milestones, and feature tracking.
- **[`../BOUNTIES.md`](../BOUNTIES.md)**: Guide to formal math prize competitions (Justin Sun Prize, conjectures.io, DeepMind Formal Conjectures) and bounty triage procedures.
- **[`../AGENTS.md`](../AGENTS.md)**: Guidelines for AI agents working within the repository, including Lean 4 coding gotchas and tactic idioms.
- **[`../scripts/bounty_triage.sh`](../scripts/bounty_triage.sh)**: Utility script to search and rank solved Erdős problems with unproven Lean statements.
