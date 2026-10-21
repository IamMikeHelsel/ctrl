# C01 — Slow command filters with useful forced tracking

**PM: NO-GO for the tested full-command-filter routes. The general question remains open.**
Quality90/100: faithfulness4, reproducibility4, discriminatory value4, critique4,
actionability2, total18/20. This grades the review, not scientific success probability.
Subjective confidence is high in scoped negative results; broader usefulness is unresolved.

AI-written. Roles: root PM, inventory_math/domain, inventory_vision_robotics/inventor,
inventory_controls_safety/critic. All inherited the root model; exact runtime identifiers
unavailable. No model-family diversity claimed. Real timestamps and substantive elapsed
research duration are recorded in ../../state.json and ../../activity.jsonl.
C01 active research:647.270678 seconds (10minutes47seconds),06:00:34–06:11:22 UTC.
Preparation, post-review checks and between-turn gaps are excluded.

## Original question and provenance

Can a causal slow command filter meet the fixed0.2mm tracking task while reducing actual
jerk or command variation relative to direct control? The causal reference,0.6m endpoint,
1.5s horizon, goal arrival at.25s and old-plan retention through.255s remain unchanged.
Plant: x'=v, v'=a, a'=80(u+.01-a), initially at rest. Full-command filters retain u from
u(0)=0; direct algebraic control starts at5/48. No preview, fictitious prehistory or resets.

Sources under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/`:

- `round-summary.txt`, `controls/filter-enclosure-08/{builder,grader}/report.txt`.
- `controls/causal-stop-05/builder/{reference.json,report.txt,compare.py}`.
- `controls/admission-04/grader-preflight/preflight.txt`.

Reference SHA256:0afc2c547033e22570711ea63a4d62c8a4380499c62a5da3f644de04fce5ad02.
This was an investigated problem. Unforced stability does not prove forced tracking. The
old builder's pending-review label was stale: its independent grader accepted the exact
failure enclosures. Today's critic replayed that separate implementation with mutations.

## Crossovers, assumptions and tests

1. **Moment matching:** compensated jerk feedforward already matches direct DC error gain.
   Adding current snap matches two more low-frequency coefficients. Causality and task are
   preserved, but matching moments cannot establish transient quality.
2. **Damping and state realization:** include filter memory and redesign poles jointly with
   polynomial feedforward. Lambda20 is near the exact stability boundary18.423. Feedforward
   changes the numerator; it cannot repair weak denominator dynamics by itself.
3. **Unexpected delay-distribution analogy:** a positive causal smoothing kernel is a
   distribution of delays. Zero mean delay forces mass at zero. Inverse differentiation can
   cancel smoothing; lambda20 alone does not bound slew with unrestricted filter input.
4. **Convexity and viability:** the one-snap-gain family has affine sampled histories, allowing
   a whole sampled feasible-interval cost test. A robust jerk cap spends braking authority
   under disturbance uncertainty and fails tracking. A relocated slow feedforward correction
   is a separate architectural lead, not success for the original full-command filter.

Root independently implemented a causal derivative blend using nominal dynamics, excluding
unknown disturbance from its controller calculation. The critic independently reconstructed
physical ODEs. Details, mappings, falsifiers and exact assumptions are in the three role notes
and pm_analysis.md. Tests use actual jerk and command variation, not reference smoothness.

## Results that change what to try next

- The two original filters fail0.2mm tracking with exact Python interval witnesses whose
  lower endpoints are1.259612313705mm and0.335036376680mm.
- Six predetermined damping-plus-feedforward designs meet sampled tracking but lose both
  peak jerk and command variation to direct. The optimized sampled one-snap-gain family also
  loses jerk-squared integral and variation. This is not a universal optimization certificate.
- The strongest joint design has an analytic tracking bound near0.118381mm. Nevertheless,
  actual jerk at t=.05s exceeds11.93122m/s³ by a rational exponential enclosure. Independently
  checked convolution reasoning bounds direct actual jerk globally below
  22451/1920=11.693229m/s³. Its peak-jerk disadvantage therefore does not depend on a time
  grid. Command-variation comparisons remain numerical.
- Any controller meeting this task needs peak jerk at least60499239/6083500=9.944807923m/s³,
  from a rational-time position witness and an integral bound. This is necessary, not an
  optimum or a claim of attainability.
- A slow filter only in a feedforward correction preserves fast direct feedback. Fixed
  gain1/960 slightly improves sampled command variation and jerk-squared integral at nine
  discrete rate/disturbance points. Peak jerk worsens in two. At fixed rate80, hand convolution
  reasoning gives an all-time tracking bound0.0515625mm for any bounded |w|<=.01, using exact
  reference Bernstein certificates. This alternative changes filter placement and does not
  answer the original full-command-filter question.

## Independent critique and evidence level

The critic independently checked transfers, Routh conditions, historical exact enclosures,
physical-coordinate integrations for baseline/retunes/blends/six co-designs/18 robustness
trajectories, exact reference Bernstein certificates and the analytic jerk separation.
Numerical reproduction discrepancies are at most about5.4e-11 in reported metrics. Controls
that corrupt dynamics, initialization, timestamps, retained states, derivative terms,
Bernstein coefficients, coverage and range are rejected.

New analytic bounds are ordinary mathematics with exact rational checks, independently
reviewed; **not Lean kernel proofs**. No novelty, physical stopping, actual travel-corridor
safety, hardware validation, noisy sensing, saturation, delay, or continuous uncertain-rate
certification is claimed. No solver-only output is accepted as proof. Original research and
approved Lean challenges remain unchanged. Primary literature links and their limited role
are recorded in pm_analysis.md.

## PM decision and precise next action

Close blind tuning of these tested full-command families. Retain direct as baseline; a new
proposal must model initial filter state and optimize actual jerk/variation subject to the
original tube. Record the relocated-feedforward result as an architectural connection for
C02's scheduled review, only if its frozen scope permits it; C02 is not reviewed here and its
coefficient question must not silently become a dynamic-filter question. No C01 extension is
scheduled. Continue S12, then frozen order; all60 initial reviews precede GO extensions.

Artifacts: domain.md, inventor.md, critic.md, pm_analysis.md, their scripts and JSON results.
