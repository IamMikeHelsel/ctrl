# Library map validation — 22 October 2026

Scope: 13 opportunity records, a consumer-oriented site page, research deep links and a work
accounting ledger. No numerical implementation, frozen statement, workflow or package API changes.

## Executed locally

- `uv run ruff check .`: pass.
- `uv run ruff format --check .`: pass, 20 files.
- `uv run pytest -q`: 67 passed, 1 integration test deselected.
- `node --check site/consumers.js`: pass.
- Independent reviewer: all 13 JSON records agree with HTML cards, field/route mappings,
  source links and research fragment sets. All relative links across five pages resolve.
- Independent execution of the actual filter script: all 15 field/relationship combinations
  and both change handlers pass, including zero-result cases.
- Desktop browser: vision gives OpenCV/YOLO (2); vision plus existing research dependency gives
  0; all fields plus existing dependency gives MuJoCo, CVXPY/OSQP and python-control/SciPy (3).
  The S12 link opens the corresponding research card.
- Independent accounting: 60 completed initial reviews, 55 GO / 1 HOLD / 4 NO-GO,
  M05-B01 the only completed extension, S12-B01 partial at 551.661992 seconds;
  55 formal-library modules and 445 named headline audit entries.

## Limits

This is a proposed integration map. No downstream integration, performance gain, external
adoption, physical robot behavior, Rust parity or PLC compiler acceptance was demonstrated.
Browser checks used the desktop viewport; no device or narrow-screen browser acceptance claimed.
The exact-head self-hosted checks and final merge status are recorded on the pull request.
The existing live Pages site is deployed from a separate branch; merging does not publish this page.
