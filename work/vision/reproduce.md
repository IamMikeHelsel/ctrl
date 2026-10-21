# Reproduce the overnight timing work

AI-assisted research artifacts, October 18–19, 2026. These are simulations and an exact-rational
reference implementation; no physical robot was connected or commanded.

## Evidence and commands

From `/Users/mike/Dev/ctrl`:

```sh
uv run experiments/tremor.py --output work/vision/tremor-results.json
uv run experiments/tremor_feedback.py
uv run experiments/tremor_report.py
uv run experiments/timing_replay.py
uv run pytest -q tests/test_tremor.py tests/test_timing_contract.py
cd lean
lake env lean Research/CoveringFamily.lean
lake env lean Research/TimingContracts.lean
```

The first command saves 740 visual-reference comparisons and clock/velocity probes. The second
saves 248 direct 1 kHz feedback comparisons. PEP 723 headers pin the numerical dependencies for
those experiments without changing the project's ordinary CLI dependencies. The plotted report
is `tremor-summary.png`; paired comparison gates and raw differences are in `tremor-analysis.json`.

The original 740-run source is frozen as `tremor-results-source.py`; its SHA256 matches the
results file. The subsequent feedback experiment freezes both its driver and the amended
plant implementation as `feedback-source-tremor_feedback.py` and `feedback-source-tremor.py`.
Use the frozen versions together when reproducing an old result. The current source also fixes
empty-convergence reporting (`null`, not success); the 740-run snapshot predates that fix but
actually executed six passing checks, so its convergence result is unaffected. The early pilot
is superseded by the corrected batch and is not the primary reproducibility artifact.

`*-traces/` folders contain acquisition/receipt/sequence/position observations, actuation times,
and noise traces. They are synthetic chosen stress conditions, not empirical robot statistics.
Stochastic cases use ten seeds; deterministic cases use one. Numerical convergence checks cover
RMS/peak motor jerk, RMS/peak tracking error, and RMS torque at 50 vs25 microsecond integration.
Phase and saturation are recorded but are not part of those convergence aggregates.

## What the timing sink does

`experiments/timing_contract.py` is a reference library with exact `Fraction` arithmetic:

- `Observation` carries a nonnegative integer clock epoch and sequence, an acquisition-time
  interval, estimated position/velocity, and their error bounds.
- `TimingSink.ingest` rejects duplicate/reordered sequences, globally inconsistent time intervals, and wrong
  epochs. A signaled reset requires a strictly increasing epoch and clears old state.
- `TimingSink.at(execution_time)` returns `ready` with a predicted center/radius, or an explicit
  reason (`no_state`, `expired`, or acquisition not definitely in the past). It does not silently
  turn stale state into an actuator command or choose a plant-specific fallback.

If acquisition is in `[lo,hi]`, execution is after `hi`, midpoint is `c`, age bound is `H=t-lo`,
and clock halfwidth is `δ=(hi-lo)/2`, the center and radius are

    center = qhat + vhat*(t-c)
    radius = ep + ev*H + abs(vhat)*δ + A*H²/2.

`Research.TimingContracts.timed_prediction_error` kernel-checks the underlying real-number
error algebra. Its model obligation is explicit: trajectory displacement has remainder at most
`A*h²/2`, together with the declared position, velocity, and time-error bounds. Neither that
physical model nor the Python state machine is automatically verified by the algebra theorem.
Exact rational arithmetic avoids pretending floating arithmetic is an outward-rounded interval.
It also makes this a specification/reference implementation, **not a qualified 1 kHz runtime**.

The PM/root audit found and fixed three concrete guard failures: NaN sequence values bypassed
ordering checks, reused clock epochs enabled replay, and adjacent interval overlap could hide
an impossible global capture order. Regression tests now cover those cases. The third repair
retains the largest accepted lower endpoint, rejects an upper endpoint below it, and clears
that constraint on reset. It tests existence of a nondecreasing sequence of possible capture
times, not the true hidden order. It leaves the observation interval unchanged for conservative
prediction. Already returned prediction objects cannot be revoked by resetting the sink;
consumers must re-query at application rather than queue unversioned predictions.
A hidden clock/model violation can still be observationally indistinguishable from valid data;
receipt-only checks cannot guarantee detection. This is not a safety, stability, or passivity
certificate for a closed-loop robot, and no new timing algorithm is claimed.

## Primary baselines

The Ruckig Community package performs local offline planning and evaluates the trajectory at
actual application time. No intermediate-waypoint cloud API or Pro subscription is used.
The freshness adapter is compared against the same estimator, planner limits, and traces.
[Official Ruckig example](https://github.com/pantor/ruckig/blob/main/examples/02_position_offline.py).

The estimator sweep calls the authors' released OneEuroFilter package, plus explicitly coded
causal least-squares and variable-step Kalman baselines.
[Author implementation](https://github.com/casiez/OneEuroFilter/tree/main/python).

Both timestamp correction and filtering are established ideas. The current engineering result
is a reproducible demonstration of their effect under stated assumptions, not evidence that
most real-robot tremor has this cause. Closed-loop reversal/reset behavior, broader
plant/gain sweeps, real telemetry, and runtime qualification remain future experiments.

## Exact reversal and signaled-reset replay

`timing-replay/results.json` records a separate analytic replay, not additional plant runs.
Its source snapshots and full rational query traces are stored alongside it. The trajectory
`q(t)=t−t³/3` on `[0,2]` has a velocity reversal at `t=1`, acceleration bounded by 4,
and constant jerk −2. Fifty-hertz synthetic observations carry 2 ms clock halfwidth, explicit
position/velocity error bounds, delayed and duplicate packets, a blackout, and a signaled
epoch reset. The first new-epoch packet is delayed 10 ms to expose the empty-state interval.
Queries run at 1 kHz; this tests semantics, not runtime deadline performance.

With a valid acceleration bound, all 1,813 ready predictions enclose the exact position.
There are 141 expired, 37 not-definitely-past, and 10 no-state queries; those return no center.
Two old-epoch arrivals and 105 reordered/duplicate arrivals are rejected. With the same trace
and a deliberately false zero acceleration bound, 120 ready predictions miss the truth.
This negative control demonstrates the dependence on the supplied physical-model bound.

An independent finite oracle enumerates possible capture assignments for 1,000 interval
chains and checks 3,000 accept/reject decisions. All match the repaired history-aware guard.
This is exhaustive only on the stated four-point grid; the general feasibility argument is
elementary greedy interval propagation and is not claimed as novel or Lean-certified here.
No time-integration convergence test is needed for exact rational polynomial evaluation.
Clock calibration, automatic reset detection, actuator fallback, cached-command revocation,
closed-loop reversal response, and physical motion are outside this replay.
