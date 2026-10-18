INDEPENDENT NATIVE-EXECUTION-06 REVIEW

Read review-report.txt and grade.json after the final review manifest is present.
The prior 05 native-clock failures stay frozen in latency-noise-05/grader.

Pre-run evidence:
  contract-review.json          Frozen-input scope review
  native_oracle.py              Independent native history from frozen 05 tools
  native-oracle.json            All independent native plans/polynomial schedules
  oracle-before-primary-manifest.json
                               Oracle hash record before reading 06 schedules
  preflight_review.py           Exact comparison against frozen 06 primary plans
  preflight-review.json         Passing preflight before plant execution
  source-audit.txt              Native state carry and export review

Final evidence:
  final_fidelity_review.py      Fresh native replay of every saved native query
  final-fidelity-review.json    Fixed q/v/a limits and preservation results
  physical_replay.py            Independent 80-digit physical ODE replay
  physical-review.json          All rows, metrics, events and task decisions
  reference_bounds.py          Exact executed-piece extrema and join gaps
  jump_variation.py             Exact command-jump variation from reference pieces
  variation-interpretation.txt  Why very short phases change jump-sensitive TV
  check_variation_metrics.py    Compare exact jump algebra with physical metrics
  summarize_review.py           Task/metric comparison with accepted 05 model data

The physical replay uses .tools/research-python/bin/python (mpmath). Other review
scripts use python3. physical_replay.py and final_fidelity_review.py each take the
final builder artifact manifest hash as their sole argument. The preflight script
checks its fixed pre-run manifest. No script should overwrite this frozen review.
For reproduction, copy scripts to a new sibling of grader with the same parent
builder relationship. Preserve relative access to frozen 05, or change paths only
in that reproduction copy and record the change. Native caches are excluded from
preservation; build them from the recorded pinned sources/runtime if absent.

Run physical_replay.py and final_fidelity_review.py after verifying the final
builder freeze. Then run summarize_review.py and check_variation_metrics.py.
The exact reference bounds and jump audit use frozen schedules and need no
physical simulation. High precision is numerical evidence, not a Lean proof.
