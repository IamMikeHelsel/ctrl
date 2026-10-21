# Proposal 05: Discrete LQR / Kalman / LQG Theory, from Existence to Separation

**Status**: Delivered, kernel-checked, standard axioms only, 0 `sorry`
**Roadmap items closed**: §3.2 (DARE), the converse-Lyapunov gap, steady-state Kalman, LQG stability

## Module chain

```
LQR ──────────────┐
ConverseLyapunov ─┴─► DAREExistence ─► SchurLyapunov ─► DAREUniqueness ─┬─► LQROptimality
                                                                        └─► Estimation/SteadyStateKalman ─► LQG
                                                                 Observer ─┘
```

| File | Headline theorem | Statement |
|---|---|---|
| `Controls/DAREExistence.lean` | `dare_exists_of_certificate` | Riccati value iteration from 0 converges to the **minimal** PSD DARE solution, given a stabilizing certificate |
| | `dare_standard_form` | The limit satisfies P = Q + AᵀPA − AᵀPB(R+BᵀPB)⁻¹BᵀPA |
| `Controls/SchurLyapunov.lean` | `converse_lyapunov_of_schur` | Aᵏx → 0 ∀x ⇒ ∃ S ⪰ 0, AᵀSA − S = −Q (removes the convergence assumption from `ConverseLyapunov`) |
| | `lqr_exists_of_stabilizable` | (A,B) stabilizable, Q,R ≻ 0 ⇒ positive definite DARE solution with stabilizing gain |
| `Controls/DAREUniqueness.lean` | `dare_le_of_stabilizing` | The stabilizing solution is the **maximal** PSD solution |
| | `dare_unique_of_posDef` | Q ≻ 0 ⇒ at most one PSD DARE solution |
| | `lqr_existsUnique_of_stabilizable` | Existence, uniqueness, convergence and stability in one statement |
| `Controls/LQROptimality.lean` | `riccatiIter_le_lqrCost` | x₀ᵀP_N x₀ ≤ N-step cost of **every** input sequence |
| | `lqr_infinite_horizon_optimal` | The feedback u = −Kx has total cost exactly x₀ᵀPx₀; every finite-cost input costs at least that much |
| `Estimation/SteadyStateKalman.lean` | `kalman_steady_state` | (A,C) detectable, W,V ≻ 0 ⇒ unique PSD filtering-ARE solution Σ ≻ 0; covariance iteration converges; A − L(Σ)C is Schur stable |
| | `kalman_observer_error_tendsto_zero` | The steady-state Kalman predictor drives the `Observer.lean` error to 0 for every input |
| `Controls/LQG.lean` | `tendsto_zero_of_schur_forced` | Converging input, converging state: Schur-stable A with forcing d → 0 gives x → 0 |
| | `lqg_closed_loop_stable` | **Separation principle, dynamical form**: LQR gain + steady-state Kalman gain stabilize the output-feedback loop |

Numeric companion: `scripts/dare_numeric_check.py`. It runs value iteration exactly as
`riccatiIter` defines it and compares the result with `scipy.linalg.solve_discrete_are` on an
open-loop unstable plant (ρ(A) ≈ 1.61). Results: agreement to 1e-14, monotone iterates, and
closed-loop spectral radii < 1 for the LQR, Kalman and LQG loops.

## Proof ideas worth reusing

- **Loewner order through quadratic forms** (`LoewnerLE`, `SymPSD`). Every inequality reduces to a
  scalar `linarith`.
- **Polarization** (`tendsto_polarMatrix`). Pointwise convergence of quadratic forms gives
  convergence of symmetric matrices. Monotone convergence then works in the Loewner cone without a
  matrix norm.
- **Continuity of the Riccati map**: factor it as `P ↦ (P, (R+BᵀPB)⁻¹)` followed by a polynomial
  map, and use `continuousAt_matrix_inv`.
- **Pointwise to uniform contraction** (`exists_pow_contraction`): column-sum bounds turn
  `Aᵏx → 0` into `‖Aᴺx‖ ≤ ½‖x‖`. This gives geometric decay without spectral theory.
- **Duality**: the Kalman results are obtained from the LQR results applied to (Aᵀ, Cᵀ, W, V),
  plus `schur_transpose`.

## Natural follow-ups

1. Detectability version of LQR: relax Q ≻ 0 to (A, Q^{1/2}) detectable.
2. Continuous-time ARE and Kalman–Bucy filter (roadmap §3.3).
3. LQG cost optimality, beyond stability (needs probability: expected quadratic cost).
4. Robustness: LQR guaranteed gain/phase margins (discrete-time disk margin).
