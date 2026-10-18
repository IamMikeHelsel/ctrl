Five-minute mathematical capability trials — prepared 17 October 2026

Purpose
Give every problem in our bounded catalog a diagnostic attempt, even when we
are not prepared to solve it. The output should improve our understanding of
capabilities and missing prerequisites. A five-minute failure is not evidence
that the mathematics is impossible or beyond the model in a longer session.

Scope and budget
The pinned Erdős catalog contains 1,221 entries, including known solved/disproved
problems as separately labeled calibration cases. It is not every question
Erdős ever asked. At 300 seconds each it needs 101 h 45 m of serial active time, before
statement retrieval, dependency preparation and model warmup. The 12 curated major
problem/competition task cards are a separate queue, adding one serial hour.
The combined metadata queues contain 1,233 entries (102 h 45 m active time). Running several heavy
models concurrently on one GPU may reduce throughput; measure before scheduling.

Preparation before the timer
1. Pin the actual mathematical statement, source URL/commit, bytes/hash and
   latest status. Metadata alone cannot serve as the problem statement. Record
   claims/conflicts and formal statement dependencies without assuming proof.
2. Supply a small source-faithful task card, a fixed model identifier/settings,
   toolchain/lockfile and bounded tool access. Warm the model outside active time;
   record preparation and load time separately. Do not disclose a known solution
   in the calibration prompt; model pretraining contamination remains possible.
3. Validate the machine/model/checker loop on a known valid theorem, a false
   statement, a malformed proof, a changed statement and a forced timeout.
4. Freeze the queue. Preserve failed/time-limited attempts. Resuming creates a
   new attempt tied to the same problem, not a rewritten success record.

The 300-second active trial (guideline, not rigid per-phase timeouts)
0–45s: restate the exact target, assumptions and what would count as progress.
45–180s: attempt ONE argument, counterexample family, construction or useful lemma.
180–270s: run the appropriate checker or try to refute the proposed step.
270–300s: save the outcome, actual checked scope, failed approaches, missing
knowledge/tooling and the best concrete next task. Preserve incomplete output.
All reasoning, tool calls and repair attempts fit within the active wall clock.
Post-trial independent review has its own separately recorded cost.

Outcome fields (keep these separate)
- execution: completed / timed_out / adapter_failed / runner_failed;
- mathematical artifact: none / conjectural_argument / finite_experiment /
  checked_counterexample / checked_component / candidate_full_proof;
- verification: not_run / rejected / passed_exact_stated_target;
- relevance: exact_target / special_case / conditional / weakened_or_changed;
- knowledge gap: statement / domain_theorem / search_idea / formal_library /
  computation / integration / resource_limit;
- follow-up: exact next lemma/test, required source and estimated work class;
- novelty/publication/prize: unknown until independent semantic/literature review.
No single model-written score or 'proof complete' string counts as acceptance.
Known-problem calibration, open research, finite checks and formal components
must have separate denominators. Report censored/time-limited results explicitly.

Files and usage
  python3 research/problem-trials/prepare_queue.py
  python3 research/problem-trials/test_trial_runner.py
  python3 research/problem-trials/trial_runner.py --case READY_CASE.json \
    --adapter-argv CONFIGURED_ADAPTER.json --seconds 300
Adapter config is a JSON argv array, executed directly without a shell. Its stdin
is the case JSON; TRIAL_OUTPUT_DIR and TRIAL_BUDGET_SECONDS describe the attempt.
The adapter must implement the model/tool/checker loop; none is configured here.
Credentials should come through the existing runtime, never argv or task files.
The runner writes an immutable attempt directory with logs, input hash, command
hash and timeout status. It never executes model output or marks a theorem solved.
Tests use only local dummy processes; they are not model capability evidence.

Current readiness
sparky-readiness.json is a read-only check. SSH and the existing Leanstral model
were reachable. Lean/Lake were not found on the noninteractive command PATH in
the initial check, but both executables exist under ~/.elan/bin. Previous
two model calls returned no candidate. The full 300-second model/tool/checker loop
has NOT passed calibration. No broad sweep, remote install or service change was
made. These files prepare the work; they do not claim the machine is ready.

The existing daily 40-percentage-point shared-account allowance remains a ceiling,
not a compute target. A future full sweep must retain that budget boundary where
account-backed models are used. Local GPU wall time is a separate resource.
