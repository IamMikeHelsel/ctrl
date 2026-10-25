# Proposal: Discrete Algebraic Riccati Equation & LQR Completion of Squares

**Module**: `ControlsLean/Controls/DARE.lean`  
**Status**: Delivered (algebraic core)  
**Toolchain**: Lean 4 `v4.36.0-rc1`

## Motivation

The Discrete Algebraic Riccati Equation (DARE) is the steady-state fixed point of discrete-time LQR and the dual of the Kalman filtering Riccati. `ctrl` already had scalar Riccati convergence (`Estimation/RiccatiConvergence.lean`) and multivariate Joseph-form Kalman optimality (`Estimation/KalmanOptimality.lean`). This module supplies the matching control-side identity: the matrix Bellman completion of squares that characterizes the optimal LQR gain and yields closed-loop Lyapunov stability on any DARE solution.

## Scope (delivered)

1. **Input Gramian** `S = R + Bᵀ P B` with symmetry and PSD preservation.
2. **Inverse-free optimal gain equation** `S K* = Bᵀ P A` (dual to `K* S = P Cᵀ` in Kalman).
3. **DARE operator at an optimal gain** `𝒯(P) = Aᵀ P A − (K*)ᵀ S K* + Q`.
4. **Bellman residual** `M(K)` encoding `ℓ(x, −Kx) + V((A−BK)x) − V(x)`.
5. **Completion of squares**: `M(K) = 𝒯(P) − P + (K − K*)ᵀ S (K − K*)`.
6. **Closed-loop cost decrease** on DARE solutions and asymptotic stability via `DiscreteLyapunov`.

## Non-goals (deferred)

- Existence and uniqueness of the stabilizing PSD solution under controllability / detectability.
- Operator monotonicity and contraction of `𝒯` on the PSD cone.
- Explicit duality isomorphism with the filtering Riccati / Joseph update.

## Novelty relative to LeanForControl / Mathlib

LeanForControl formalizes discrete Lyapunov *equations* `Aᵀ P A − P = −Q` for Schur `A`, but not the LQR/DARE completing-the-square calculus or gain optimality. Mathlib has no DARE or LQR content. This module is the first machine-checked inverse-free DARE/Bellman identity in the `ctrl` ecosystem, deliberately mirroring the Joseph-form Kalman pattern already in the library.

## References

* Anderson, B. D. O., & Moore, J. B. (1971). *Linear Optimal Control*. Prentice-Hall.
* Lancaster, P., & Rodman, L. (1995). *Algebraic Riccati Equations*. Oxford University Press.
* Hespanha, J. P. (2018). *Linear Systems Theory* (2nd ed.), Chapter 20.
