## 2026-10-19T05:54:04Z
You are worker_m4_math.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/worker_m4_math.
Write your notes, progress, and handoff to your working directory. Update progress.md regularly.

CRITICAL INSTRUCTION:
Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md before doing anything else.
Also read:
- /Users/mike/dev/ctrl/PROJECT.md
- /Users/mike/dev/ctrl/.agents/teamwork/explorer_survey_math_1/handoff.md
- /Users/mike/dev/ctrl/docs/crossover-program-report-2026-10-18.md (evidence tiers, prior 44.5189 SDP bound)

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

Your assigned scope (Milestone 4: Math — Rational Dual SDP Certificates for Discrete Energy Bounds):
1. Exclusive write ownership:
   - `/Users/mike/dev/ctrl/tools/sdp_rational_cert.py`
   - `/Users/mike/dev/ctrl/tests/test_sdp_rational_cert.py`
   Do NOT touch any other source or test files. Sibling repos are strictly read-only.
2. Implement `/Users/mike/dev/ctrl/tools/sdp_rational_cert.py`:
   - Tool bridging floating-point numerical SDP solvers (cvxpy / clarabel / scs) to exact kernel-checkable rational certificates.
   - Formulates quadratic energy / Lovász theta / flag SDP relaxations:
     $\min \langle C, X \rangle$ s.t. $\operatorname{diag}(X) = 1, X \succeq 0$.
     Dual: $\max \sum y_i$ s.t. $S = C - \operatorname{diag}(y) \succeq 0$.
   - Implements rational projection: perturbs the floating-point dual vector $\tilde{y}$ into an exact rational vector $y_{\mathbb{Q}} \in \mathbb{Q}^n$ such that $S_{\mathbb{Q}} = C - \operatorname{diag}(y_{\mathbb{Q}}) \succ 0$ is guaranteed strictly positive definite.
   - Computes the exact rational $L D L^\top$ Cholesky decomposition over $\mathbb{Q}$ with unit lower-triangular $L$ and all diagonal entries $D_i > 0$.
   - Verifies the identity $L D L^\top \equiv S_{\mathbb{Q}}$ symbolically and in exact rational arithmetic, proving an exact mathematical lower bound $\sum y_{\mathbb{Q}, i}$ without floating-point error.
   - Exports the certificate to JSON format with exact fraction string representations.
   - Evaluates on standard benchmark instances (e.g., triangle graphs, hypergraph cuts, and 5-cycle / Petersen graph bounds).
3. Implement `/Users/mike/dev/ctrl/tests/test_sdp_rational_cert.py`:
   - Comprehensive test suite testing rational matrix arithmetic, rational $L D L^\top$ factorization, strict positive definiteness preservation, numerical-to-rational perturbation, and certificate generation across multiple graph topologies.
   - Ensure 100% pass rate: `cd /Users/mike/dev/ctrl && uv run pytest -v tests/test_sdp_rational_cert.py`.
   - Ensure full suite passes without regressions: `uv run pytest -q`.
   - Ensure clean `uv run ruff check`.
4. Deliver complete report in `/Users/mike/dev/ctrl/.agents/teamwork/worker_m4_math/handoff.md`.
When complete, notify caller via `send_message`.
