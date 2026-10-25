# Task Assignment: Erdős 273 Independent Audit & Verification Worker

## Objective
Implement an independent, standalone audit verifier `work/273/check_eleven.py` for the 11-smooth covering extension certificate, including rigorous mutation checks, and formalize the verification test suite.

## Working Directory
`/Users/mike/dev/ctrl/.agents/teamwork/worker_273_audit`

## Mandatory Integrity Warning
DO NOT CHEAT. All verifications and certificates must be genuine. DO NOT hardcode test results or fabricate verification outputs. A teamwork_preview_auditor will independently verify your work.

## Detailed Scope
1. Exclusive write ownership:
   - `/Users/mike/dev/ctrl/work/273/check_eleven.py`
   - `/Users/mike/dev/ctrl/tests/test_covering_273.py`
2. Technical Implementation:
   Follow the blueprint from `/Users/mike/dev/ctrl/.agents/teamwork/explorer_lanes_273_885_1/handoff.md` Section 4.1:
   - Read `/Users/mike/dev/ctrl/work/273/check_seven.py` for architecture and mutation test methodology.
   - Read `/Users/mike/dev/ctrl/work/273/smooth_probe.py` and `work/273/probe-11-symmetric.json`.
   - Implement `/Users/mike/dev/ctrl/work/273/check_eleven.py`:
     (a) Standalone replays the 3,518-node conditional capacity tree without external search solvers or floating-point rounding.
     (b) Recomputes the geometric tail for 5 primes ($p \le 11$) exactly: $\text{tail} = \frac{1806085527193}{7116137582400000}$.
     (c) Verifies the uncovered survivor count and density gap (> 4.08%) at every branch.
     (d) Implements 4 adversarial mutation tests in `mutation_checks()`:
         - Mutate the root period or prefix modulus.
         - Tamper with a tree node capacity bound (e.g. artificial inflation).
         - Tamper with the geometric tail bound.
         - Mutate a branch residue offset.
         Verify that ALL 4 mutations are caught and rejected with explicit integrity errors!
3. Tests & Regression:
   - Implement `tests/test_covering_273.py` running the 7-smooth audit (`check_seven.py`) and 11-smooth audit (`check_eleven.py`).
   - Run `uv run python work/273/check_eleven.py`.
   - Run `uv run pytest -v tests/test_covering_273.py`.
   - Run `uv run ruff check work/273/check_eleven.py tests/test_covering_273.py`.
   - Run full regression `uv run pytest -q`.
4. Deliver your complete report to `/Users/mike/dev/ctrl/.agents/teamwork/worker_273_audit/handoff.md`.
When done, notify caller via `send_message`.

## 2026-10-19T07:07:42Z
Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md and /Users/mike/dev/ctrl/.agents/teamwork/worker_273_audit/DISPATCH.md.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/worker_273_audit.
Write only to your working directory. Update progress.md regularly with timestamped progress.

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All verifications and certificates must be genuine. DO NOT hardcode test results or fabricate verification outputs. A teamwork_preview_auditor will independently verify your work.

Your assigned scope:
Implement standalone independent audit verifier work/273/check_eleven.py for the 11-smooth covering extension certificate, including rigorous mutation checks, and add test suite.
1. Exclusive write ownership:
   - /Users/mike/dev/ctrl/work/273/check_eleven.py
   - /Users/mike/dev/ctrl/tests/test_covering_273.py
2. Follow the blueprint from /Users/mike/dev/ctrl/.agents/teamwork/explorer_lanes_273_885_1/handoff.md Section 4.1:
   - Read /Users/mike/dev/ctrl/work/273/check_seven.py for architecture and mutation test methodology.
   - Read /Users/mike/dev/ctrl/work/273/smooth_probe.py and work/273/probe-11-symmetric.json.
   - Implement work/273/check_eleven.py:
     (a) Standalone replays the 3,518-node conditional capacity tree without external solvers.
     (b) Recomputes 5-prime geometric tail (p <= 11) exactly: tail = 1806085527193 / 7116137582400000.
     (c) Verifies uncovered survivor count and density gap (> 4.08%) at every branch.
     (d) Implements 4 adversarial mutation tests in mutation_checks():
         1. Mutate root period or prefix modulus.
         2. Tamper with a tree node capacity bound.
         3. Tamper with the geometric tail bound.
         4. Mutate a branch residue offset.
         Verify that ALL 4 mutations are caught and rejected with explicit errors!
3. Verification:
   - uv run python work/273/check_eleven.py
   - uv run pytest -v tests/test_covering_273.py
   - uv run ruff check work/273/check_eleven.py tests/test_covering_273.py
   - uv run pytest -q (zero regressions)
4. Deliver your complete report to /Users/mike/dev/ctrl/.agents/teamwork/worker_273_audit/handoff.md.
When complete, notify caller via send_message.
