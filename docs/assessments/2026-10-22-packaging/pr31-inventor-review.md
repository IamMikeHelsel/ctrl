# PR 31 independent code review

Reviewed 22 October 2026, AI-assisted, without changing the shared checkout or submitting a GitHub review. Exact head: `a7d6d55cf247f5597cf1f4a920f74711330325fe`. [PR 31](https://github.com/IamMikeHelsel/ctrl/pull/31) was draft, mergeable and `CLEAN`; both reported Lean Action CI `build` checks succeeded. Those checks exercise Lean CI, not the new Python tests.

Recommendation: fix the two concrete interface/validation findings before calling this tool ready for agent consumption. The shipped data and happy paths work; this is not a finding against the underlying research ideas. Root retains the merge decision. No merge, publication or external message was performed.

## Findings

1. **P2: JSON mode emits plain text on expected failures.** In `tools/ctrl_cli/synergy.py`, `run_synergy_cli` checks unknown IDs/domains and no-path results before the JSON branch. Reproduced with `uv run --no-project python ctrl synergy unlock DOES-NOT-EXIST --json` and `... rank --domain invalid --json`: both exit 2 and print plain text to stdout. A caller consuming the advertised JSON interface cannot decode the error. Return an explicit machine-readable error/no-path object in JSON mode, preserve nonzero status, and test these CLI paths.

2. **P2: schema validation runs after unsafe construction and omits numeric constraints.** `SynergyGraph._load` accesses IDs and coerces numeric fields before `validate` runs (`synergy.py:128–130`, `:495–500`). A candidate with `effort_weeks="bad"` raises `ValueError`; removing its ID raises `KeyError` rather than producing validation diagnostics. More materially, `payoff=NaN` and `effort_weeks=-2` both return an empty validation-error list. The former propagates `NaN` into rank JSON, which is not standard JSON; the latter removes the effort penalty and excludes the item from the proposed plan. Validate raw shape, types, finite numeric ranges and effort semantics before constructing a graph; reject nonfinite serialization and test malformed scout inputs. Python's JSON parser also accepts a standard exponent token such as `1e309` as infinity, so this is not limited to spelling a nonstandard `NaN` token.

## Evidence

The exact GitHub tarball was expanded into `/tmp/ctrl-pr31-review-a7d6d55`; no checkout/reset occurred. Only that disposable snapshot was used for experiments. Python ran via `uv run --no-project` because this snapshot has no Python project manifest.

- All 11 supplied tests passed (`python -m unittest discover -s tools/tests -v`, 0.007 seconds reported by unittest). Two unclosed-file resource warnings occurred in the site-index test; these are minor cleanup, not a correctness blocker.
- The shipped graph validates: 96 nodes, 360 idea edges, 66 domain edges. The 12- and 26-week greedy plans contain no missing candidate dependencies in this particular dataset. This does not prove general dependency-aware scheduling; the method is documented as greedy selection.
- Rebuilding `site/synergy.html`, `site/SYNERGY_WEIGHTS.json`, and `docs/RESEARCH_FRONTIER_2026-10.md` reproduced all three checked-in files byte-for-byte.
- Code and tests for loading, scoring, path search, scout merging, report generation and site rendering were inspected. Failure-mode tests above were independent additions in the disposable snapshot; no PR source was modified.
- No Lean files changed in the PR; existing successful Lean CI was inspected rather than rebuilding an unrelated environment. The current workspace's full Ruff/pytest/`ctrl check --all` commands do not describe this other repository-layout snapshot and were not presented as passing.

Scope: this is a bounded code/interface review, not verification of every source citation or every numerical estimate in the 76-candidate frontier. Scores, confidence and effort estimates remain planning judgments. The merge should not promote them to independently verified facts.
