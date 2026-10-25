# BRIEFING — 2026-10-19T07:08:00Z

## Mission
Implement exact rational semidefinite / algebraic certificate tools for real 6x6 Byers-Nash pairs on the active mf13 lane.

## 🔒 My Identity
- Archetype: worker
- Roles: implementer, qa, specialist
- Working directory: /Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_cert
- Original parent: 0b6a5e14-8c10-4497-8beb-fd637698bacb
- Milestone: mf13 rational certification

## 🔒 Key Constraints
- Exclusive write ownership: /Users/mike/dev/ctrl/tools/certify_mf13_pair.py, /Users/mike/dev/ctrl/tests/test_mf13_rational_cert.py, and /Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_cert/*
- DO NOT CHEAT: all implementations must be genuine, maintain real state, compute exact rational certificates. No hardcoding test results or dummy/facade implementations.
- Zero regressions on `uv run pytest -q`.
- Equality sets (rank-4 ridge, common-T locus) have margin 0, so strict SDP ($S \succ 0$ with positive slack) cannot exist there.
- At/near equality sets, must use non-strict / exact-SOS certificates (e.g. algebraic Common-T involution pairing <YT, L_A(KT)> = ||Y||^2).
- Interior SDP domain handles pairs with positive margin via exact rational LDL^T.
- Full hypothesis audit compliance: no hidden slack or assumed margins.

## Current Parent
- Conversation ID: 0b6a5e14-8c10-4497-8beb-fd637698bacb
- Updated: not yet

## Task Summary
- **What to build**: Exact rational semidefinite / algebraic certificate tools for real 6x6 Byers-Nash pairs on the active mf13 lane.
- **Success criteria**:
  - `uv run python tools/certify_mf13_pair.py` passes
  - `uv run pytest -v tests/test_mf13_rational_cert.py` passes
  - `uv run ruff check tools/certify_mf13_pair.py tests/test_mf13_rational_cert.py` clean
  - `uv run pytest -q` passes without regressions
  - Genuine exact certificates for Card M05 candidate pairs, calibration pair diag(J, 2J, 3J) at A = (1/2)I_6, and common-T involution candidates.
- **Interface contracts**: PROJECT.md / SCOPE.md
- **Code layout**: tools/, tests/

## Change Tracker
- **Files modified**:
  - `tools/certify_mf13_pair.py`: Exact rational semidefinite and algebraic certificate tools for 6x6 Byers-Nash pairs.
  - `tests/test_mf13_rational_cert.py`: Comprehensive test suite for linear algebra, Common-T certifier, 21x21 dual SDP, Gram tester, and tamper rejection.
- **Build status**: All checks passed (python tools/certify_mf13_pair.py, pytest tests/test_mf13_rational_cert.py: 9 passed in 2.86s, ruff check: clean, pytest -q: 200 passed in 14.87s).
- **Pending issues**: None.

## Quality Status
- **Build/test result**: All passing (200 passed across repo, 9 passed in new test suite).
- **Lint status**: Clean (ruff check passes with zero errors/warnings).
- **Tests added/modified**: `tests/test_mf13_rational_cert.py` (9 tests covering linear algebra, calibration, Common-T, Card M05 at t=1/2 and t=1/3, 21x21 dual SDP, and tamper rejection).

## Loaded Skills
- None specified in dispatch

## Key Decisions Made
- Implemented stratified certificate architecture per Track B blueprint and parent guidance:
  1. Exact algebraic SOS Common-T Involution Certifier for the 8D equality locus (k=s=1), verifying <YT, L_A(KT)> = ||Y||^2 identically with zero slack needed.
  2. Full 21x21 rational dual SDP certifier with exact LDL^T > 0 (all 21 pivots positive) on calibration pair.
  3. Exact 9x9 rational Gram quadratic tester certifier with exact LDL^T > 0 (all 9 pivots positive) and optimal minimizer z* on Card M05 candidate pairs (t=1/2, t=1/3).
  4. Automatic solver and certifier for rational Common-T involutions and conjugated families.

## Artifact Index
- DISPATCH.md — task assignment
- BRIEFING.md — persistent working memory
- progress.md — liveness tracker
- handoff.md — final handoff report (pending)
