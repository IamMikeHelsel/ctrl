# Research log

## 2026-10-18 local / 2026-10-19 UTC

- Selected273 after checking current discussions. Several catalog stepping stones were stale.
  Existing pod lanes885/939/MF13 were left untouched.
- Rejected unconditioned weighted capacity: class maxima are at least their averages, so
  it cannot improve the reciprocal-density obstruction.
- Derived conditional CRT capacity on a small period. Program manager independently checked
  the formula and finite-cover interpretation of the infinite tail.
- Seven-smooth, first large box: exact Python pruning excluded all assignments.
- Simplified to prefix4,6,10,12 and a small exponent box; an independent small-divisor sieve
  plus all720 residue assignments gives minimum margin342/60000=57/10000.
- Eleven-smooth, short prefix: the bound was inconclusive, with8280 unresolved leaves.
  Adding30 and36 closes it:594323 baseline nodes; with translation stabilizers3518 nodes.
- Spark job20261019-052014-273-solve-8226 failed immediately on invalid input48, since49
  is composite. This was an execution/configuration error, not a negative mathematical result.
  Outputs were fetched; none were produced. The local eleven-smooth success did not use48.
- Kernel certification and a larger exploratory family are in progress; see plan.md and
  the program manager report for the distinction between finite certificates and a full theorem.
- The valid Spark thirteen-smooth job `20261019-052643-273-solve-298c` returned its output
  after 240 seconds: 89,700 nodes, 57,567 pruned, 26,952 unresolved leaves, and a time limit.
  The process exited successfully because it saved a result; the mathematical result is
  **inconclusive**, with `excluded_by_python_bound=false`. Its artifact was fetched.
- Kernel checks passed finite mass bounds, the arbitrary finite geometric-tail theorem,
  conditional CRT counting, and exact periodic lift cardinality. Final composition remains open.
- Python: 55 tests passed. Lint and format pass outside concurrent `work/pod/`; the whole
  lint run reported 119 findings there at the latest snapshot. That count can change as the
  other agents work. No concurrent files were repaired or reformatted.
- `ctrl check --all`: 834 builds, audits, and binds correctly; it remains NOT_APPROVED.
  Problem 273 has no approved challenge or solution and is skipped by that check.
- Overnight continuation created as `erd-s273-overnight-proof-and-review`; hourly in this
  chat, with a 07:00 Pacific October19 stop condition and continued program-manager review.
- Integrated `lake build` completed successfully (8,970 build jobs, mostly cached).
  All printed new theorem axioms are among propext, Classical.choice, Quot.sound.
  This includes the finite residue certificate, its capacity-to-uncovered-point theorem,
  the sieve and mass certificate, finite geometric tail, and both CRT/lift counting lemmas.
  It does not supply the still-missing theorem assembling those pieces for every admissible family.
- 2026-10-18 spark solve job `20261019-052643-273-solve-298c` started
- 2026-10-18 fetched job `20261019-052643-273-solve-298c` → work/273/candidates/20261019-052643-273-solve-298c/
- Schedule correction: the original hourly heartbeat was paused after Mike objected.
  His subsequent explicit request for specific overnight self-checkins authorized
  replacement with 23:30 October 18 and 01:30, 04:30, 07:30 October 19 Pacific.
  The tool accepted and persisted an UNTIL cutoff of October 19 14:30 UTC.
  Pause sooner when complete, canceled, superseded, or non-actionable; no automatic
  extensions or checkins on dead threads. Unrelated automations were left unchanged.
- `CoveringAssembly.pool_capacity_bound` now passes Lean: finite reciprocal group
  bounds imply the capacity expression for arbitrary `U`, including the reserved
  tail budget. The proof's axioms are only propext, Classical.choice, Quot.sound.
  Initial attempts exceeded elaboration limits through unfolding the large pool;
  explicit arithmetic rewrites and a local irreducibility attribute resolved this
  without increasing the heartbeat limit or adding trust. Full family assembly is
  still incomplete. Added the module to the integrated Research target.
- Fresh Python suite: 106 passed, 1 deselected. Targeted Ruff for experiments,
  problem 273, and this lane's tests passed. Whole-repo Ruff reported 495 errors;
  format reported 71 files needing changes in the concurrently changing tree,
  including work/pod, .agents/teamwork, and other agents' Lorentz files. Those files
  were not edited. These are snapshot counts, not persistent baseline claims.
- 2026-10-18 fetched job `20261019-052643-273-solve-298c` → work/273/candidates/20261019-052643-273-solve-298c/

- Integrated checkpoint build passed: 8,971 jobs. All four printed Assembly theorems
  use only propext, Classical.choice, Quot.sound. ctrl check --all again confirms
  834 builds/audits/binds and stops only at NOT_APPROVED; 273 has no solution and
  is skipped. No Challenge file was changed. The full seven-smooth theorem and
  novelty remain unestablished; the next obligations are saved in checkpoint.json.

- Full seven-smooth theorem completed: CoveringFamily.seven_smooth_period_gap and
  seven_smooth_not_cover passed direct Lean compilation and the integrated8,972-job
  build, with only propext/Classical.choice/Quot.sound. Independent program-manager
  faithfulness audit passed. Complete family quantifiers, arbitrary integer residues,
  unbounded exponents, and57/10000 period gap are explicit. Novelty is not established.
  Latest user priority is now robot tremor experiments, with eleven-smooth secondary.

- Final integrated checkpoint8973jobs passed, including the conditional timing-error
  algebra theorem. FullPython164passed1deselected.988simulationcomparisons and14
  step-halving checks are saved underwork/vision; the new freshness rule hadzero
  qualifyingwins overRuckig. Direct1kHz nominal-vs-actual derivative experiment
  supports a classical timing-error mechanism, not a newalgorithm or prevalenceclaim.
  The PMmorningreport remains scheduled for07:30Pacific; finite overnightcontinuation
  must not redo finishedwork or revive canceled/superseded threads.

- Morning delivery checkpoint October19 07:30Pacific: root and program manager verified all10 problem273 and14 vision manifest entries, with no drift. No proof build or experiment rerun. Morning report finalized at work/vision/morning-report-2026-10-19.md; automation paused through the app tool and scheduler verified PAUSED with no next run. Seven-smooth remains proved, novelty unestablished; no new robotics algorithm or hardware claim.
- 2026-10-19 `ctrl new 273`: drafted challenge from FC `Erdos273.erdos_273.variants.three`
- 2026-10-19 proved `lean/ErdosLab/Erdos273.lean` (12-modulus strict covering system of `ℕ` modulo 360 with moduli `p - 1` for primes `p ∈ {3, 5, 7, 11, 13, 19, 31, 37, 41, 61, 73, 181}` ≥ 3; 0 `sorry`, standard axioms) and `lean/Research/CoveringEleven.lean` (11-smooth and 13-smooth Euler products and finite-box tail bounds).
- 2026-10-19 fetched job `20261019-052643-273-solve-298c` → work/273/candidates/20261019-052643-273-solve-298c/
