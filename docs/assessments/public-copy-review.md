# Public homepage and README copy review

AI-written review, 2026-10-22. Worktree: `adoption-and-contribution/ctrl`. Scope: `site/index.html` and, after expanded assignment, README introduction, maturity/availability table and runtime availability wording. No mathematical source, assets, research runtime or public API changed.

## Changes

- Led with engineering goals: braking limits, modeled motion losses, disturbance tracking, camera depth, estimation and integration.
- Distinguished the public Lean checkout from the separate Python/C99/Structured Text/MuJoCo research checkout. The runtime is not installed by cloning this branch.
- Preserved all nine original HTML IDs, including `#combinations`, all four animation assets and both code examples. The walkthrough remains, with its fixed-size loop correctly described and its admissible-backup and implementation obligations stated.
- Kept reported simulation numbers, explicitly tied to their configured tasks and baselines. Separated total modeled motor loss, dynamic modeled Joule loss and the 1D theoretical result. Removed the claim that eta=-11 universally minimizes combined hardware energy.
- Removed physical SOCP-equivalence, sub-100ns PLC execution, universal deterministic timing, zero solver failure, production verification, universal one-ULP equivalence and implied thermal-validation claims. Numerical absolute error is labeled as a reported finite differential-test result.
- Changed catalog badges to **Documented results / In work**, with status counts computed from the embedded data:14 families,11 documented-result families,3 in-work families. These are distinct from48 registered research functions:42 domain functions,4 benchmarks and2 code-generation helpers. Removed unexplained novelty/application-grade badges from the visible cards; the underlying data fields remain untouched.
- Added concrete integration work to every application and combination: plant/measurement identification, calibration, timing, uncertainty, actuator limits, implementation validation and matched baselines. Percentages from separate metrics or experiments are not added.
- Added homepage links to `adopt.html` and the repository's forthcoming `CONTRIBUTING.md`; README links to both local documents. Their implementation belongs to the coordinating agent.
- Replaced the README production-readiness matrix and “90%+ proved” framing with availability/evidence layers. Preserved the detailed mathematical module map and technical proof descriptions for a separate theorem audit.

## Checks performed

1. Parsed old/new HTML: every original ID retained, no duplicate IDs, all local anchor references resolve, all four image paths exist and both preformatted code examples remain.
2. Ran the actual inline JavaScript in Node with a minimal DOM harness: initial14 cards,11/3 status filters, intersection with the Math domain, reset to14, and dynamic count labels all passed.
3. `git diff --check` passed after removing one introduced whitespace-only line.

These are structural/functional checks, not a rendered desktop/mobile browser review. No Lean build was repeated for copy-only changes; repository-wide build/workflow acceptance remains with the coordinator. Reported historical simulation and C timings were not rerun, and their full source environment is not present here.

## Remaining source and adoption boundaries

- The machine-readable `site/AGENT_IDEA_INDEX.json` contained stronger stale readiness/novelty labels. The coordinator owns its scope warning; this edit did not silently rewrite that separate index.
- The repository retains detailed historical research and mathematical claims elsewhere. This focused copy review is not an independent reproof of those claims. In particular, the historical MF-13 prose should be reconciled against its exact operator-norm definition before it is reused in a new technical exposition.
- The recorded visual-servo angle differed between README (155 degrees) and homepage (160 degrees). The homepage now says the documented large camera roll rather than inventing a reconciled value. Reproduction should pin the original run configuration.
- Some catalog combination IDs reference an absent `ROBO-04`; these are existing text identifiers, not newly broken hyperlinks. Resolve them when revising the catalog's source schema.
- No production, hardware, thermal, compiler-equivalence or worst-case timing certification follows from these edits. The adoption guide should offer one bounded usable component first and separately name the work needed for a larger integrated benefit.

## Independent workflow/contribution review

Read the four workflow YAML files, `CONTRIBUTING.md`, `docs/SELF_HOSTED_VERIFICATION.md`, the Lake target configuration, Dockerfile and `scripts/check.sh`. Refreshed [GitHub dispatch semantics](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#workflow_dispatch), [secure-use guidance](https://docs.github.com/en/actions/reference/security/secure-use), and the [Lean action's own definition](https://raw.githubusercontent.com/leanprover/lean-action/v1/action.yml). No workflow was dispatched and no runner/repository setting was changed by this critic.

**Required verification fix identified:** the reviewed Lean workflow ended with the default Lean action and did not invoke the repository's `scripts/check.sh`. The Lake default target is the library only; the upstream action's axiom-audit input defaults to false. A normal Lean build can succeed with `sorry` warnings. Therefore the workflow did not establish the contribution policy's explicit escape-hatch/headline-axiom gate. Sent to the workflow owner and coordinator for an explicit full audit step or equivalent. Recheck the final edited workflow before counting this resolved.

**Publication remains blocked on an external policy gate, correctly documented:** fork contributors can propose new workflow YAML, so these checked-in filters alone cannot protect persistent self-hosted machines once public. The policy explicitly requires an administrator-level fork gate before visibility changes and reports that it could not be verified while private. Keeping the repository private is consistent with readiness preparation. Read-only tokens, Docker and branch naming are correctly described as insufficient isolation. No new direct PR/PR-target/workflow-run trigger or privileged fork-code checkout was found in the reviewed four files.

**Exact SHA association is accurately scoped:** trusted-branch pushes run against their event SHA. Manual-main dispatch checks out an explicit reviewed SHA, with an environment variable and lowercase40-hex validation; its GitHub check association remains the main dispatch event. The policy warns not to count that as an external PR's required check. A reviewed acknowledgement is a human trust decision, not proof of code safety. New integration commits require their own evidence.

**Remaining declared trust:** third-party action tags and fetched tool/dependency releases are mutable upstream inputs. This was already present and the policy mentions external build inputs; it is not a claim of hermetic verification. Lint and shellcheck remain advisory by design, while formatting is blocking. A green lint job does not mean no findings. The local `scripts/check.sh` lexical ban currently names sorry/admit/axiom; the stronger AGENTS prohibition on native_decide/implemented_by relies on additional review and the selected headline audit, not a whole-tree lexical ban of those terms.

**Adoption/pipeline checks:** JSON and rendered HTML agree on60 unique initial reviews:55GO,1HOLD,4NO-GO;12 per domain and10 wildcard candidates. S12 is labeled partial, with one completed extension elsewhere. GO is explained as a next-test decision, not a deployable product. The42 domain functions,48 total registrations and14 catalog families are kept distinct. All local fragment links on adopt/pipeline resolve. The serial benefit formula is correctly labeled illustrative and separates stage share, stage reduction and overhead; its result is not a YOLO measurement. Browser layout and final full workflow execution are separate coordinator checks.
