# Dispatch: Milestone 6 Independent Reviewer (reviewer_m6_1)

## Mission
Perform comprehensive independent verification of all research artifacts across Math, Controls, and Vision produced on branch `crossover-research-2026-10-19`.

## Working Directory
`/Users/mike/dev/ctrl/.agents/teamwork/reviewer_m6_1`

## Mandatory Reference Documents
Read before executing:
- `/Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md`
- `/Users/mike/dev/ctrl/PROJECT.md`
- `/Users/mike/dev/ctrl/AGENTS.md`

## Verification Scope & Commands
1. Lean 4 Kernel Checks:
   Run each command in `/Users/mike/dev/ctrl/lean`:
   - `lake env lean Research/LorentzConeCBF.lean`
   - `lake env lean Research/HomographyDecomposition.lean`
   - `lake env lean Research/CentroidalDecelerationLimit.lean`
   - `lake env lean Research/VisualServoingInvariant.lean`
   - `lake env lean Research/SkewNormalForm.lean`
   - `lake env lean Research/SkewRankFourNormalForm.lean`
   Verify exit code 0, 0 sorry, and check axioms (must be standard `[propext, Classical.choice, Quot.sound]` only).

2. Erdős 273 Covering Systems:
   Run in `/Users/mike/dev/ctrl`:
   - `uv run python work/273/check_eleven.py`
   - `uv run pytest -v tests/test_covering_273.py`
   Verify 3,518-node tree replay, exact 5-prime tail, and that all 4 adversarial mutation tests are rejected.

3. Erdős 885 Quadric Intersection & Mazur Rank:
   Run in `/Users/mike/dev/ctrl`:
   - `uv run python tools/verify_885_geometry.py`
   - `uv run pytest -v tests/test_885_geometry.py`
   Verify 21 Jacobian minors symbolic non-vanishing, $g=49$, Mazur rank $\ge 1$ across 20 covering curves, and obstruction certificate.

4. Byers–Nash $n=6$ (`mf13`) Exact Rational Dual SDP Certifier:
   Run in `/Users/mike/dev/ctrl`:
   - `uv run python tools/certify_mf13_pair.py`
   - `uv run pytest -v tests/test_mf13_rational_cert.py`
   Verify 21x21 exact rational $LDL^\top \succ 0$ factorization and Common-T involution verifier on 8D equality locus.

5. Full Test Suite & Linter:
   Run in `/Users/mike/dev/ctrl`:
   - `uv run pytest -q`
   - `uv run ruff check .`
   Verify 100% pass rate and clean lint.

## Deliverable
Deliver your comprehensive review report to `/Users/mike/dev/ctrl/.agents/teamwork/reviewer_m6_1/handoff.md` with an explicit verdict: APPROVE or REQUEST_CHANGES.
When done, notify caller via `send_message`.


## 2026-10-19T08:21:48Z
Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md and /Users/mike/dev/ctrl/.agents/teamwork/reviewer_m6_1/DISPATCH.md before doing anything else.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/reviewer_m6_1.
Write only to your working directory. Update progress.md regularly with timestamped progress.

Your mission:
Perform comprehensive independent review and verification of all research artifacts across Math, Controls, and Vision on branch crossover-research-2026-10-19:
1. Lean 4 Kernel Checks:
   In /Users/mike/dev/ctrl/lean, run:
   - lake env lean Research/LorentzConeCBF.lean
   - lake env lean Research/HomographyDecomposition.lean
   - lake env lean Research/CentroidalDecelerationLimit.lean
   - lake env lean Research/VisualServoingInvariant.lean
   - lake env lean Research/SkewNormalForm.lean
   - lake env lean Research/SkewRankFourNormalForm.lean
   Verify exit code 0, 0 sorry, and check axioms.
2. Erdős 273 Covering Systems:
   In /Users/mike/dev/ctrl, run:
   - uv run python work/273/check_eleven.py
   - uv run pytest -v tests/test_covering_273.py
   Verify 3,518-node tree replay, exact tail, and that all 4 mutation tests are rejected.
3. Erdős 885 Quadrics & Obstruction:
   In /Users/mike/dev/ctrl, run:
   - uv run python tools/verify_885_geometry.py
   - uv run pytest -v tests/test_885_geometry.py
   Verify 21 Jacobian minors symbolic non-vanishing, g=49, Mazur rank >= 1, and obstruction certificate.
4. Byers–Nash n=6 (mf13) Exact Rational Dual SDP Certifier:
   In /Users/mike/dev/ctrl, run:
   - uv run python tools/certify_mf13_pair.py
   - uv run pytest -v tests/test_mf13_rational_cert.py
   Verify 21x21 exact rational LDL^T > 0 factorization and Common-T involution verifier on 8D equality locus.
5. Full Regression & Linter:
   In /Users/mike/dev/ctrl, run:
   - uv run pytest -q
   - uv run ruff check .

Deliver your complete review report to /Users/mike/dev/ctrl/.agents/teamwork/reviewer_m6_1/handoff.md with a clear verdict: APPROVE or REQUEST_CHANGES.
When done, notify caller via send_message.
