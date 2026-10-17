# ControlsLean

Machine-checked results in controls, estimation, and machine vision, built on Mathlib
(Lean `v4.36.0-rc1`). Every file is `sorry`-free, and each headline theorem depends only on
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Results

| Area | File | Headline theorems |
|---|---|---|
| Machine vision | `ControlsLean/Vision/Epipolar.lean` | `epipolar_constraint`, `det_essential`, `vecMul_essential`, `collinear_iff_det` |
| Controls (small) | `ControlsLean/Controls/Hurwitz2.lean` | `isHurwitz2_iff`, `massSpringDamper_hurwitz` |
| Estimation (small) | `ControlsLean/Estimation/ScalarKalman.lean` | `postVar_eq_opt_iff`, `inv_postVarOpt`, `riccati_fixed_unique`, `riccati_lipschitz` |
| Controls (medium) | `ControlsLean/Controls/Reachability.lean` | `reach_eq_reach_finrank`, `controllable_iff_finrank`, `Controllable.exists_steer`, `controllable_feedback` |
| Stability (medium) | `ControlsLean/Controls/DiscreteLyapunov.lean` | `tendsto_pow_mulVec_zero`, `PosDef.tendsto_pow_mulVec_zero` |

Notes on what is new relative to Mathlib:

* **Reachability** proves that reachable subspaces stabilize at `n = dim V` by counting
  dimensions along the reachable-subspace chain, without Cayley–Hamilton. Reachability is
  linked to actual trajectories (`mem_reach_iff`) and shown invariant under state feedback.
* **Discrete Lyapunov** needs no symmetry assumption on `P` and gives a geometric rate
  (`exists_lyapunov_contraction`).
* **Epipolar** holds over any field and for any matrix `R`, not only rotations.

## Workflow

Build artifacts live in `~/lean-work/ControlsLean` (the Mathlib cache is ~5 GB and must not
sync through Drive). Only sources are mirrored to Google Drive.

```bash
source ~/.elan/env
cd ~/lean-work/ControlsLean
scripts/check.sh ControlsLean/Controls/Foo.lean   # fast loop on one file (~5 s)
scripts/check.sh                                  # full build + sorry ban + axiom audit
git add -A && git commit -m "..."
scripts/sync.sh                                   # mirror sources to Drive/lean/ControlsLean
```

Loop per target: state the theorem in a new file, then run `check.sh` on that file and fix
errors until it is clean. Add the file to `ControlsLean.lean` and its headline theorems to
`scripts/Audit.lean`, then run the full check, commit, and sync.

## Backlog (next targets, roughly by size)

Small:
* Discrete-time Jury test for degree 2: roots of `z² + a z + b` lie in the unit disk iff
  `|b| < 1` and `|a| < 1 + b`.
* Homography: the composition and inverse of projective maps act on homogeneous points.
  Four-point correspondence uniqueness.
* Convergence of the scalar Riccati iteration to `steadyState` (contraction is already proved).

Medium:
* Observability as the dual of controllability: `(A, C)` observable iff `(Aᵀ, Cᵀ)` controllable.
  Unobservable subspace stabilization.
* Converse Lyapunov: Schur-stable `A` admits `P = Σ (Aᵀ)ᵏ Q Aᵏ`.
* Pole placement for single-input controllable systems (controllable canonical form).
* Eight-point algorithm correctness: `E` is determined up to scale by 8 generic correspondences.

Larger:
* Continuous-time Lyapunov via the matrix exponential.
* Kalman filter optimality in the matrix (multivariate) case.
