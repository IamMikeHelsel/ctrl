# Task Assignment: Worker Fix M5 Label & Update Project

## Objective
1. In `/Users/mike/dev/ctrl/tools/push_sdp_cert.py` and `/Users/mike/dev/ctrl/tests/test_crossover_push.py`:
   - Remove the mislabeled `(mf13)` tag from `certify_lyapunov_contraction` and rename references to `toy_lyapunov_contraction` (or `centroidal_toy_lyapunov`).
   - Clearly document in docstrings and comments that this is a "Toy 4x4 Lyapunov stability example", NOT the real 6x6 Byers-Nash mf13 lane.
2. Copy `/Users/mike/dev/ctrl/.agents/teamwork/orchestrator_1/PROJECT.md` to `/Users/mike/dev/ctrl/PROJECT.md`.
3. Verify:
   - Run `uv run python tools/push_sdp_cert.py`
   - Run `uv run pytest -v tests/test_crossover_push.py`
   - Run `uv run ruff check .`
   - Run `uv run pytest -q`
4. Deliver your handoff report to `/Users/mike/dev/ctrl/.agents/teamwork/worker_fix_m5_label/handoff.md`.

## 2026-10-19T06:55:14Z
Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md and /Users/mike/dev/ctrl/.agents/teamwork/worker_fix_m5_label/DISPATCH.md.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/worker_fix_m5_label.
Write only to your working directory. Update progress.md regularly with timestamped progress.

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

Your assigned scope:
1. In /Users/mike/dev/ctrl/tools/push_sdp_cert.py and /Users/mike/dev/ctrl/tests/test_crossover_push.py:
   Remove the mislabeled '(mf13)' tag from certify_lyapunov_contraction and rename references to toy_lyapunov_contraction (or centroidal_toy_lyapunov).
   Clearly document in docstrings and comments that this is a 'Toy 4x4 Lyapunov stability example', NOT the real 6x6 Byers-Nash mf13 lane.
2. Copy /Users/mike/dev/ctrl/.agents/teamwork/orchestrator_1/PROJECT.md to /Users/mike/dev/ctrl/PROJECT.md.
3. Verification commands:
   - cd /Users/mike/dev/ctrl && uv run python tools/push_sdp_cert.py
   - cd /Users/mike/dev/ctrl && uv run pytest -v tests/test_crossover_push.py
   - cd /Users/mike/dev/ctrl && uv run ruff check .
   - cd /Users/mike/dev/ctrl && uv run pytest -q
4. Deliver your complete report in /Users/mike/dev/ctrl/.agents/teamwork/worker_fix_m5_label/handoff.md.
When complete, notify caller via send_message.
