# BRIEFING — 2026-10-19T06:06:00Z

## Mission
Implement exact rational dual SDP certificates (`tools/sdp_rational_cert.py`) bridging floating-point numerical SDP solvers to verified rational lower bounds via LDL^T Cholesky over Q, and comprehensive test suite (`tests/test_sdp_rational_cert.py`).

## 🔒 My Identity
- Archetype: worker
- Roles: implementer, qa, specialist
- Working directory: /Users/mike/dev/ctrl/.agents/teamwork/worker_m4_math
- Original parent: 0b6a5e14-8c10-4497-8beb-fd637698bacb
- Milestone: Milestone 4: Math — Rational Dual SDP Certificates for Discrete Energy Bounds

## 🔒 Key Constraints
- Exclusive write ownership:
  - `/Users/mike/dev/ctrl/tools/sdp_rational_cert.py`
  - `/Users/mike/dev/ctrl/tests/test_sdp_rational_cert.py`
  - `/Users/mike/dev/ctrl/.agents/teamwork/worker_m4_math/` (agent metadata)
- Do NOT touch any other source or test files. Sibling repos are strictly read-only.
- Integrity mandate: No hardcoding test results, dummy/facade implementations, or shortcut strategies.
- Ensure 100% test pass rate and clean ruff check.
- Keep handoff self-contained with 5-component structure.

## Current Parent
- Conversation ID: 0b6a5e14-8c10-4497-8beb-fd637698bacb
- Updated: 2026-10-19T05:54:30Z

## Task Summary
- **What to build**: Tool `tools/sdp_rational_cert.py` converting floating-point SDP solutions (cvxpy/clarabel/scs) for energy/Lovász theta/flag relaxations into exact rational certificates with strictly positive definite dual slack $S_{\mathbb{Q}} \succ 0$, rational $L D L^\top$ factorization, JSON certificate export, and testing suite in `tests/test_sdp_rational_cert.py`.
- **Success criteria**:
  - Exact rational matrix arithmetic and rational $L D L^\top$ decomposition over $\mathbb{Q}$ ($L$ unit lower-triangular, $D_i > 0$).
  - Perturbation / rounding heuristic guaranteeing $S_{\mathbb{Q}} = C - \operatorname{diag}(y_{\mathbb{Q}}) \succ 0$.
  - Exact symbolic/rational identity verification: $L D L^\top \equiv S_{\mathbb{Q}}$, guaranteeing a valid lower bound $\sum y_{\mathbb{Q}, i}$.
  - Support for quadratic energy, Lovász theta, Max-Cut / binary quadratic programs.
  - JSON serialization with fraction strings.
  - Benchmarks: triangle graph, 5-cycle, Petersen graph, hypergraph cut.
  - 100% test pass rate (`pytest -v tests/test_sdp_rational_cert.py` and full suite `pytest -q`).
  - Clean `ruff check`.
- **Interface contracts**: `/Users/mike/dev/ctrl/PROJECT.md`
- **Code layout**: `/Users/mike/dev/ctrl/PROJECT.md`

## Key Decisions Made
- Implemented `RationalMatrix` using Python standard library `fractions.Fraction` for zero-dependency exact arithmetic.
- Implemented rational $L D L^\top$ decomposition without square roots (exact rational operations only: additions, multiplications, divisions by positive pivots).
- Implemented a self-contained primal-dual barrier interior point solver using Jacobi eigendecomposition and Newton's method on the log-barrier objective, with optional automatic delegation to CVXPY (Clarabel / SCS) if present.
- Implemented dynamic epsilon-perturbation that pushes floating-point dual boundary vectors strictly into $\mathbb{S}_{++}^n$ while controlling denominator explosion via `limit_denominator`.
- Benchmarked exact graph topologies including reproducing the crossover report's 44.5189 bound on Erdős 834 Li hypergraph cut.

## Artifact Index
- `/Users/mike/dev/ctrl/.agents/teamwork/worker_m4_math/DISPATCH.md` — Dispatch prompt
- `/Users/mike/dev/ctrl/.agents/teamwork/worker_m4_math/BRIEFING.md` — Working memory and identity
- `/Users/mike/dev/ctrl/.agents/teamwork/worker_m4_math/progress.md` — Progress tracker
- `/Users/mike/dev/ctrl/tools/sdp_rational_cert.py` — Exact rational SDP certificate tool
- `/Users/mike/dev/ctrl/tests/test_sdp_rational_cert.py` — Comprehensive unit test suite (25 tests)

## Change Tracker
- **Files modified**:
  - `tools/sdp_rational_cert.py`: Implemented exact rational matrix arithmetic, rational $L D L^\top$, barrier solver, perturbation projection, certificate export, and benchmarks.
  - `tests/test_sdp_rational_cert.py`: Implemented 25 tests covering arithmetic, decomposition, positive definiteness preservation, tamper rejection, SOS evaluation, and benchmark instances.
- **Build status**: 131 tests passed in 3.25s (100% pass rate).
- **Pending issues**: None.

## Quality Status
- **Build/test result**: Pass (25/25 new tests pass, 131/131 full suite passes).
- **Lint status**: Clean (`uv run ruff check tools/sdp_rational_cert.py tests/test_sdp_rational_cert.py` reports all checks passed).
- **Tests added/modified**: 25 new tests in `tests/test_sdp_rational_cert.py`.

## Loaded Skills
- None explicitly assigned
