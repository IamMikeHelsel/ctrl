# Public-readiness preparation: validation

22 October 2026. AI-assisted implementation with domain and independent critic review. Repository visibility and the separately deployed `site` branch are unchanged.

## Scope

Contribution/PR/issue guidance; benefit-first homepage/README copy; adoption diagram and latency calculator; dated60-question GO/HOLD/NO-GO pipeline; seven-claim novelty review; explicit self-hosted trust policy and actual Lean source/axiom gate. No runtime Rust package or new YOLO acceleration is delivered.

## Local checks

- `uv run ruff check .` and `uv run ruff format --check .`: PASS in this main-based checkout.
- `uv run pytest -q`:60passed,1deselected. Sixteen source-guard tests cover forbidden code, nested comments, ordinary/raw strings, interpolation, character literals and rejection exit codes.
- `actionlint`1.7.7 with shellcheck: PASS; only unknown custom-label warnings suppressed after live label verification.
- Shell syntax and `git diff --check`: PASS.
- Four site pages: local links, assets and anchors PASS.60unique pipeline rows,12perfield,10wildcards;55GO/1HOLD/4NO-GO. M05 uses completed-extension evidence; S12 is explicitly partial.
- Static interaction harness: seven latency-calculator cases and24filter combinations PASS. Browser:5%default savings,6%overhead→1%loss,101%input rejected; NO-GO filter shows4, NO-GO+vision shows0. Desktop visual layout inspected; narrow-screen behavior has CSS/static review, not a device-browser acceptance claim.
- `uv run erdos check --all`: local run INCOMPLETE because this fresh checkout lacked the separate Mathlib cache; owned rebuild stopped. No local theorem failure or success inferred. Exact candidate self-hosted run is required before merge.

## Independent review findings resolved

- Green default Lean Action builds did not run the required source-policy/headline-axiom audit. Added explicit `scripts/check.sh` after the build and setup-uv.
- Expanded lexical checks to cover `native_decide` and `implemented_by`, with comment/string-aware cases. This source guard is not a complete Lean parser or a replacement for kernel and dependency audits.
- Copied research documents now state their source checkout. No available-main runtime package claim.
- Updated M05's pipeline evidence after the completed extension, retaining S12's partial status.

## Outstanding boundaries

Public-fork administrator policy remains unverified while private (API422). No automatic fork execution onto persistent local hosts is acceptable. See `docs/SELF_HOSTED_VERIFICATION.md`.

PR31 was independently reviewed at `a7d6d55cf247f5597cf1f4a920f74711330325fe`:11supplied tests and generated artifacts pass, but JSON-error/schema validation defects remain. It is not merged by this change. PR26's existing failed CI is also not bypassed.

The campaign remains paused within S12-B01 while this product work is performed; none of this time is counted as research extension time.

## Executed first candidate and independent repair

Candidate26b4298c passed all three self-hosted workflows: Lean39788575275 (55source files,445headline axiom checks), lint39788575296, Erdős39788575290 (56tests plus lab checks). An independent nested-interpolation probe nevertheless exposed a new lexical masking bug. The next revision keeps the uncertain interpolation tail unmasked, adds four regressions, and documents conservative rejection;60local tests pass. Earlier green evidence is not used to waive rerunning the repaired revision.

The separate GitHub Copilot review39788723947 did not start because of the account payment/spending-limit restriction reported by GitHub. Its logs are unavailable; check-run annotations supplied the reason. No billing change was made. This is separate from the three successful self-hosted verification workflows and the independent agent review.
