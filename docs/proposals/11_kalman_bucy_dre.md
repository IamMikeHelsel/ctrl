# Continuous-Time Kalman–Bucy Filter Generator & Differential Riccati Identities

**Module**: `ControlsLean/Estimation/KalmanBucy.lean`  
**Status**: Machine-checked (algebraic core); DRE existence/CARE convergence deferred  
**Dual of**: `Estimation/KalmanOptimality.lean` (discrete Joseph form)

## Summary

This module formalizes the continuous-time dual of the Bucy–Joseph completion-of-squares
identity. For the linear plant $\dot x = A x + w$, $y = C x + v$ with noise intensities
$Q$ and $R$, the observer $\dot{\hat x} = A\hat x + K(y - C\hat x)$ has error-covariance
generator

$$\mathcal{L}(K) = (A - KC)P + P(A - KC)^\top + Q + KRK^\top.$$

When $K^* R = P C^\top$, this collapses to the classical Differential Riccati right-hand side
$AP + PA^\top - K^*R(K^*)^\top + Q$, and for every competing gain

$$\mathcal{L}(K) = \mathcal{L}(K^*) + (K - K^*)R(K - K^*)^\top.$$

Whenever $R \succeq 0$, the Kalman–Bucy gain therefore uniquely minimizes both the Loewner
quadratic form $x^\top\mathcal{L}(K)x$ and the instantaneous MMSE growth rate
$\operatorname{tr}(\mathcal{L}(K))$. On CARE solutions ($\mathcal{L}(K^*) = 0$), every gain
produces nonnegative instantaneous trace growth.

## Headline Theorems (Audited)

| Theorem | Statement |
|---|---|
| `filterGen_transpose` | Symmetry of $\mathcal{L}(K)$ when $P,Q,R$ are symmetric |
| `filterGen_opt_eq_dre` | $\mathcal{L}(K^*) = \mathcal{R}_{K^*}(P)$ under $K^*R = PC^\top$ |
| `filterGen_completion_of_squares` | Matrix completion of squares for continuous gains |
| `filterGen_of_CARE` | On CARE solutions, $\mathcal{L}(K) = (K-K^*)R(K-K^*)^\top$ |
| `quad_filterGen_le` | Loewner optimality of $K^*$ |
| `trace_filterGen_eq` / `trace_filterGen_le` | Instantaneous-trace optimality |
| `trace_filterGen_CARE_nonneg` | Nonnegative trace growth off CARE |
| `care_lyapunov_identity` | $\mathcal{L}(K^*) = 0$ on CARE solutions |

## Explicit Non-Goals

- Picard–Lindelöf / existence-uniqueness for the matrix DRE ODE
- Monotonicity and contraction of the DRE flow on the PSD cone
- Asymptotic stability of $A - K^*C$ from a continuous Lyapunov theorem
- Filtering–control duality with the discrete DARE module (PR #27)

## References

* Kalman, R. E., & Bucy, R. S. (1961). New results in linear filtering and prediction theory.
  *Journal of Basic Engineering*, 83(1), 95–108.
* Bucy, R. S., & Joseph, P. D. (1968). *Filtering for Stochastic Processes with Applications
  to Guidance*. Interscience / Wiley.
* Anderson, B. D. O., & Moore, J. B. (1979). *Optimal Filtering*. Prentice-Hall, Chapter 7.
* Kailath, T., Sayed, A. H., & Hassibi, B. (2000). *Linear Estimation*. Prentice Hall, Chapter 9.
