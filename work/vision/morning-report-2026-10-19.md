# Morning research report — October 19, 2026

AI disclosure: prepared by the OpenAI Codex program manager subagent requested by Mike.
Finalized for the authorized 07:30 morning delivery. The delivery pass checked saved evidence
without running new experiments or builds. Dates use America/Los_Angeles unless UTC is stated.

## Current answer

**The full seven-smooth restricted-family theorem is proved.** Any finite set of distinct
moduli `m≥4`, with `m+1` prime and prime factors of `m` only in `{2,3,5,7}`, leaves at least
**0.57% uncovered in the specified shifted common period**, for arbitrary residue choices
and unbounded exponents. The root verified
`lake env lean Research/CoveringFamily.lean` with exit code zero, and both final theorems use
only `propext`, `Classical.choice`, and `Quot.sound`. The PM's independent source-level
faithfulness audit passes. The recorded integrated `lake build` passed with 8,973 jobs, including
the timing-error theorem. This does not solve problem 273 or establish priority.
**Eleven-smooth remains exact Python evidence, without a completed Lean theorem.**
The corrected robot-tremor batch is complete:
740 simulations, six passing convergence checks, and no planner failures. Correctly using
actual camera intervals gives a large improvement in a noise-free jitter test; measurement
noise substantially reduces that benefit. A second, direct 1 kHz feedback batch has 248 runs:
actual intervals instead of nominal intervals reduce jerk 92–99% under pure jitter; actual
intervals plus ordinary filtering reduce it about 78% under jitter plus encoder noise. The
freshness variant produces no qualifying win over ordinary Ruckig. These are demonstrated
known corrections, not a new control algorithm or hardware result. An exact-rational timing
prototype and a kernel-checked conditional error bound are also complete within their stated scope.
The scheduled 01:30 follow-up closes the bounded reversal/reset review: 1,813 ready predictions
have zero enclosure failures under a valid bound, while a deliberately false bound yields
120 undetected misses. A third ordering-guard defect was fixed and independently checked.

Of the **ten selected robotics/vision targets, three received synthetic probes; seven remain
proposals**. None is presented as a new vision algorithm or a hardware result. The useful
engineering result is a reproducible timing diagnosis and an explicit uncertainty/rejection
reference library. The broad claim that timing causes most real-robot tremor is unestablished.

Key artifacts: [formal theorem](/Users/mike/Dev/ctrl/lean/Research/CoveringFamily.lean),
[novelty review](/Users/mike/Dev/ctrl/work/273/novelty-review.md),
[ten-target portfolio](/Users/mike/Dev/ctrl/work/vision/portfolio.md),
[comparison figure](/Users/mike/Dev/ctrl/work/vision/tremor-summary.png),
[paired analysis](/Users/mike/Dev/ctrl/work/vision/tremor-analysis.json),
[exact replay](/Users/mike/Dev/ctrl/work/vision/timing-replay/results.json), and
[reproduction commands](/Users/mike/Dev/ctrl/work/vision/reproduce.md).

The program followed the requested order: finish seven-smooth, then test the tremor hypothesis.
An unintended 00:27 wake produced no new research. Independent inspection of the installed
scheduler found a local-time/UTC fallback and recurring-jitter issue; the root corrected the
remaining times to verified single occurrences. The 01:30 checkpoint completed the bounded
reversal/reset replay. The idle 04:30 wake was removed. This 07:30 occurrence delivers the
report and is the final checkpoint. The root paused the automation through the app tool and
verified both saved configuration and scheduler state: `PAUSED`, with no next actual or
nominal occurrence. There are no remaining scheduled runs for this program.

## What worked, what failed, and why

| Work | Evidence | What it means |
| --- | --- | --- |
| Conditional covering capacity | Independent exact checker, all 720 normalized prefix choices; minimum scaled margin 342, including the coarser kernel certificate | Retaining forced overlap gives a strict bound where raw reciprocal counting fails. |
| Seven-smooth tail | Kernel-checked finite-set bound outside the exponent box, with no upper limit on the omitted exponents | The tail is genuinely uniform over arbitrary finite selections, not extrapolated from a search cutoff. |
| Finite pool bridge | `pool_capacity_bound` compiled with only permitted axioms | Finite sieve arithmetic now bounds the analytic capacity expression; this is a component, not the family theorem. |
| Full seven-smooth family | `seven_smooth_period_gap` and `seven_smooth_not_cover` compile with only permitted axioms; independent statement audit passed | Arbitrary finite distinct admissible moduli with unbounded exponents cannot cover all integers; a shifted common period retains at least 0.57% uncovered. |
| Eleven-smooth deeper prefix | Exact Python search closes all branches; baseline and symmetry-reduced searches agree | Promising extension, but no completed formal theorem yet. |
| Thirteen-smooth search | Local node limit and Spark time limit left unresolved branches | Inconclusive; more frontier compute was deprioritized to complete the seven-smooth proof, and is now secondary to the requested tremor experiments. |
| First Spark attempt | Invalid modulus 48 rejected because 49 is composite | An input error caught by validation, not a mathematical obstruction. |
| Prior-art review | Primary-source review found the broad prefix-plus-tail method already used | Potential novelty is the specific family restriction and certificate, not the general technique. |
| Timing pilot | Clock/estimator diagnostics and 40 robot comparisons across four cases; six step-halving checks pass | Existing smoothing reduces jerk at a cost in lag; the new freshness rule has no demonstrated matched-lag win. No evidence that most real-robot tremor is timing-related. |
| Corrected timing batch | 740 comparisons, separate timing/noise controls, ten seeds for stochastic cases, one for each deterministic case | Actual-time differentiation helps substantially with pure camera jitter; noisy measurements remain an independent cause. No freshness method passes the declared comparison gate against Ruckig. |
| Direct feedback batch | 248 comparisons; eight convergence checks pass | Known actual-interval and filtering corrections give large gains when the derivative-feedback path is mistimed or noisy. This is PD, not full PID or hardware validation. |
| Target portfolio | Ten targets selected; V1–V3 probed synthetically | Seven targets remain researched proposals, not seven additional results. |

Exact evidence and source links are in `work/273/checkpoint.json`, `work/273/novelty-review.md`,
`work/273/seven-certificate-audit.json`, and `work/vision/portfolio.md`. Root-reported build
results and PM statement inspection are distinguished below; the PM has not independently
rerun the full Lean build.

## Seven-smooth statement audit

The advertised claim must cover **every finite set of distinct moduli** `m≥4`, each with
`m+1` prime and all prime factors in `{2,3,5,7}`, with **arbitrary choices of one residue per
modulus** and **no exponent bound**. It must conclude that some integer is uncovered without
assuming the critical mass, capacity, or coverage bounds as hypotheses.

The PM inspected the capacity, mass, tail, CRT, assembly, and final family sources. The
statements match their stated purpose. The assembly audit checked these obligations:

1. Represent every admissible modulus by `2^(a+1)*3^b*5^c*7^d`. Primality of `m+1≥5`
   supplies evenness; positive powers of 2 must not silently narrow the target.
2. Show every non-prefix modulus is either in the certified finite pool or has a chosen
   exponent tuple outside the tail box. Primality implies passing the small-divisor sieve.
3. Preserve distinctness in the tail sum. A chosen tuple representation is injective over
   distinct moduli simply because mapping it back recovers the modulus; unique factorization
   of all tuples need not be reproved for this step.
4. Cover arbitrary prefix choices by translation, and permit missing prefix moduli by adding
   classes. Adding classes only strengthens the system to be excluded; the final witness must
   translate back correctly, including integer residues.
5. Use a positive common period divisible by 60 and every chosen modulus. Prove the exact
   survivor count and sum the CRT bounds over that same period, rather than comparing counts
   from different periods.
6. Account for the tail scale: reciprocal density below `5/1000` contributes at most
   `60*(5/1000)=0.3` in the period-60 capacity expression. Do not confuse this with the final
   uncovered density margin `342/60000=57/10000`.
7. Apply the finite certificate to obtain an actual witness, audit permitted axioms, and
   inspect the final theorem's dependencies for unproved assumptions or an altered claim.

Audit status: `seven_smooth_period_gap` and `seven_smooth_not_cover` faithfully express the
intended claim; direct kernel compilation passed and both print only permitted axioms.
The PM read the complete proof path and found the obligations above addressed:

- `D : Finset ℕ` supplies distinctness, `r : ℕ → ℤ` allows arbitrary integer residues, and
  the four existential exponents have no bound. No capacity inequality remains a hypothesis.
- `even_smooth_representation` derives the positive two-exponent from primality and `m≥4`.
- The chosen representation map recovers each modulus. Equal represented moduli imply equal
  subtype indices, so its finite image is injective under `modulus` without assuming unique
  factorization or dropping repeated residue choices.
- `normalized_gap` excludes extra prefix classes when absent from `D`; this only shrinks the
  survivor set. Its subset proof returns a point avoiding every actual class.
- `integer_period_gap` normalizes by `(r m − r 4) mod m`, justifies the natural representative,
  and shifts the witness back by `r 4`. Negative and noncanonical residues are covered.
- The existence wrapper constructs `H=60*∏m∈D m`, proves it positive, and supplies every
  divisibility requirement. The period theorem permits `H=0` as a harmless degenerate case;
  the existence conclusion does not rely on that case.
- The density conclusion is explicitly a count on the shifted interval
  `[r 4, r 4 + H)`, at least `57/10000` of its length for a positive common period.
  It does not yet state an asymptotic-density theorem in those terms.

No approved challenge file needs to change. The scoped novelty review has not located the
specific infinite seven-/eleven-smooth exclusions; absence from that search does not establish
priority. General methodology is known.

## Tremor experiment scorecard

The first three probes are specified in `work/vision/portfolio.md`. They test acquisition-time
uncertainty, velocity estimation at irregular intervals, and command reconstruction in a
closed-loop one-joint plant. Every comparison must share the same generated event/noise trace.

| Gate | Acceptance evidence | Current result |
| --- | --- | --- |
| Correct timestamps | Constant-velocity actual-time difference is exact; arrival-time spacing is not substituted for acquisition spacing | Noiseless diagnostic passes; noisy-sine baseline sweep recorded. |
| Honest uncertainty | Conditional containment and explicit hidden-error counterexample | Zero containment violations in ten valid affine-clock runs; hidden out-of-envelope delay remains feasible and excludes truth. Fixed-offset calibration comparator now included. |
| Fair smoothing comparison | Compare the error/lag frontier against correctly timestamped differentiation, 1€, Kalman/local fitting, and Ruckig as applicable | Baselines implemented; no freshness/Ruckig pair in the corrected batch passes the declared gate, including cross-parameter comparisons. |
| Physical jerk | Include actuator dynamics; compute physical jerk from plant equations, not merely command differences | Source audit passes for motor-coordinate jerk, including smooth friction and flexible coupling. Flexible-load jerk is not reported. |
| Numerical convergence | Halving integration steps changes representative reported metrics by less than 1% | All six pilot checks pass; worst change 0.754% over jerk RMS/peak, tracking RMS/peak, and torque RMS. Phase and saturation are not included in that convergence aggregate. |
| Practical advancement | At least 20% lower RMS physical jerk, at most 5% worse tracking RMS, lag matched within 1 ms, and no increased limit violations | No new-method win. Known actual-time differentiation meets the gate in 7/10 pure-camera-jitter seeds, and 0/10 with camera jitter plus noise. |
| Competing explanations | Separate timing/noise controls, friction, saturation, resonance, blackout, reordering, and resets | Eleven plant cases complete. A separate analytic replay tests reversal/signaled-reset semantics; closed-loop reversal/reset integration remains untested. |
| Reproducibility | Saved configuration, trace, seed, method settings, metrics, and paired seed differences | Complete JSON, source snapshot with matching SHA-256, and 74 case/seed traces saved. Four deterministic cases use one seed each. |

The numerical advancement thresholds are declared engineering choices, not confidence levels.
A useful adapter can pass these tests without being a new control method. A theorem must state
delay, jitter, regularity, actuator and saturation assumptions explicitly. A passivity claim
needs a defined physical port and storage inequality; reduced jerk alone does not establish it.

The key negative result to preserve is whether ordinary correct timestamp handling or an
existing smoothing baseline explains the improvement. If it does, the contribution may be a
reliable integration library and diagnostic workflow. If gains disappear at matched lag, do
not describe simple delay as a smoothness breakthrough. If friction or resonance dominates,
the timing-only explanation fails for that model; it does not identify causes on real robots.

The PM found and corrected one overstrong requirement before implementation: receipt timestamps
alone cannot detect every delay-envelope violation or unannounced clock reset. An incorrect
timing model may remain consistent with the observations. The proposed containment guarantee
is conditional on the declared model; runtime checks can detect infeasibility, not certify
all hidden timing assumptions. The simulator can still label those violations using ground truth.

### Pilot interpretation and independent simulator review

`work/vision/tremor-pilot.json` has `status=complete`, with ten methods for each of clean,
queue/loss, friction, and resonance, using seed zero. No planner failures occurred. The source
has no future-observation access: observations become available only at receipt time, and
only the explicitly labeled oracle sees the analytic target. V3 assumes already calibrated
acquisition timestamps; it does not integrate the uncertainty from V1.

The closest same-limit lag-matched queue/loss comparison is `fresh_j100` against `ruckig_j100`:
lag differs by 0.986 ms and tracking RMS improves about 1.62%, but physical jerk RMS rises from
29.013 to 30.045 rad/s³, about **3.56% worse**. At jerk limit 30, the freshness rule lowers jerk
about 6.26% but changes lag by 7.19 ms. At limit 300 it lowers jerk about 2.11%, but tracking
RMS worsens about 8.46% and lag changes by 5.30 ms. None passes the declared advancement gate.
Clean/friction/resonance produce identical fresh and ordinary Ruckig outputs, as expected
without freshness expiration. Lower jerk from ordinary Ruckig relative to raw extrapolation
is an existing-method tradeoff with extra lag, not a new controller result.

The PM requested two changes before the larger batch: add a noise-only control because the
initial camera/servo-jitter cases also introduce position noise relative to clean; and avoid
reporting `all([])` as a successful convergence check when selected cases run no such check.
Repeated clean/friction/saturation/resonance seeds are deterministic duplicates, not ten
independent observations. These are interpretation and validation issues, not discovered
future-data leakage. Reversal, clock-reset integration, full timing/noise factorials, load
jerk, and hardware remain outside this pilot.

### Corrected full-batch scoring

The PM independently read `tremor-results.json`, matched its SHA-256 to
`tremor-results-source.py`, checked all 740 rows for finite numeric values, and rescored the
declared gate. Seven stochastic cases use ten seeds each; four deterministic cases use one
seed. Ten methods on 74 traces give 740 runs, not 740 independent experimental units. All
162 comparisons with no freshness expiration have exactly identical fresh/Ruckig reference
trajectories. There are no planner failures.

For the new freshness rule, **zero pairs** meet the combined requirement of at least 20% lower
jerk, at most 5% worse tracking, at most 1 ms lag difference, and no additional saturation.
This remains true when every tested freshness jerk limit is compared with every tested Ruckig
jerk limit on the same case/seed, rather than only comparing equal settings. It is a result
over the tested grid, not proof that no possible parameter setting could work.

The table reports means of paired percentage changes against Ruckig at the same jerk limit;
negative means lower jerk. A small average lag difference must not be mistaken for a matched
comparison in every seed.

| Stress case | Jerk limit | Mean jerk change | Paired range | Seeds within 1 ms lag | Qualifying wins |
| --- | ---: | ---: | ---: | ---: | ---: |
| Queue/loss | 30 | −2.92% | −5.29% to −0.57% | 3/10 | 0/10 |
| Queue/loss | 100 | −0.31% | −3.66% to +3.83% | 0/10 | 0/10 |
| Queue/loss | 300 | −0.40% | −2.44% to +3.02% | 3/10 | 0/10 |
| Blackout | 30 | −1.37% | −6.61% to +4.66% | 0/10 | 0/10 |
| Blackout | 100 | −0.21% | −3.53% to +2.73% | 0/10 | 0/10 |
| Blackout | 300 | +0.06% | −1.54% to +1.87% | 3/10 | 0/10 |

The useful timing signal is in a known correction. Under noise-free camera jitter, actual-time
differentiation plus extrapolation reduces jerk by a paired mean **71.59%**, with reductions
69.26–73.62%, relative to nominal-time differentiation. Tracking changes range from −3.18%
to +2.33%, and seven seeds also satisfy the 1 ms lag condition. With the same camera timing
stress plus position noise, mean jerk reduction is only **7.61%** and no seed passes the
20% threshold. Noise-only mean jerk for actual-time extrapolation is 177.78 rad/s³ versus
24.82 in the clean case; proper timestamps do not remove spatial measurement noise.

Pure servo jitter changes mean actual-time-extrapolation jerk from 24.82 to 24.84 rad/s³ in
this model. That small effect does not support a claim that 1 kHz servo jitter dominates
tremor here. V3 uses vision-target/reference updates feeding a fixed PD controller with exact
simulated joint-position/velocity feedback. It does not test a full mistuned PID with noisy or
stale proprioception, numerical derivative terms, or integral windup; the result cannot rule
out those failure modes in real 1 kHz stacks. Conversely, friction raises even the ideal-reference controller's jerk from
2.33 to 13.95 rad/s³ with perfect observation timing. These are model-specific causal
comparisons, not estimates of cause prevalence across research robots. The reduced-torque
case produces saturation for some Ruckig settings but not all methods, so it is not a uniform
severe-saturation test.

V1 retains zero containment violations under its declared affine-clock/delay model. Final
interval widths range from 0.065 to 0.576 ms. The added fixed-offset comparator calibrates
for one second using the known mean delay and has subsequent error RMS 0.391–1.948 ms.
Interval width and point-estimate RMSE are different metrics: this is not a direct numerical
accuracy ranking. The hidden-delay counterexample remains undetectable from receipt data alone.

Source review confirms separate measurement-noise RNG, noise-free pure-jitter cases,
noise-only controls, deterministic seed reduction, source snapshots, and exact nonexpired
freshness checks. The frozen 740-run source retains `all([])=True`, but the PM subsequently
verified the current implementation's `convergence_status` fix: empty checks return `None`,
with a regression test. The frozen batch is unaffected because all six checks actually ran
and passed; its snapshot correctly preserves what executed. Reversal,
reset integration, uncertainty propagation from V1 into V3, load-joint jerk, measured deadlines,
passivity, and hardware acceptance remain open.

### Direct 1 kHz feedback: why the second experiment changed the interpretation

The first model supplied exact joint velocity to the PD controller, so servo jitter could
not corrupt a numerical velocity estimate. The follow-up replaces that diagnostic shortcut
with causal finite differences of encoder position. It compares nominal-interval differences,
actual-interval differences, and actual-interval differences with a standard 100 Hz first-order
low-pass filter. A labeled true-velocity diagnostic remains. All modes share the same PD
gains, noisy position in the proportional term, event times, and noise trace. There is no
integral term: this is **PD, not full PID**.

The PM verified both source hashes, inspected the causal feedback loop, and rescored all
248 finite rows in `feedback-results.json`. The batch has 31 case/seed traces, two reference
types, and four feedback modes. Eight step-halving checks pass; the worst relative change is
0.6374% across the five checked metrics. Each comparison below uses ten paired seeds.

| Stress / correction | Ideal analytic reference: mean paired jerk reduction | Ruckig reference: mean paired jerk reduction | Full declared gate |
| --- | ---: | ---: | --- |
| Pure servo jitter: actual vs nominal interval | 99.02% | 92.16% | 10/10 seeds for each reference |
| Jitter + 20 µrad encoder noise: actual vs nominal interval | 26.45% | 26.41% | 10/10 for each |
| Encoder noise only: actual interval + 100 Hz filter vs unfiltered actual interval | 70.30% | 69.40% | 10/10 for each |
| Jitter + noise: actual interval + 100 Hz filter vs nominal interval | 78.59% | 77.93% | 10/10 for each |

The gate requires at least 20% lower jerk, tracking RMS no more than 5% worse, lag difference
at most 1 ms, and no added saturation. Every listed pair passes; mean lag changes are below
0.51 ms and tracking improves slightly. No actuator saturation occurs in this feedback batch.
Filtering is not universally beneficial: with noise-free jitter and Ruckig reference, adding
the filter to actual-time differentiation raises jerk about 2.26%.

If position moves approximately at velocity `v`, dividing its increment by a fixed interval
produces `v_hat≈v*actual_interval/nominal_interval`. Jitter becomes a fluctuating derivative
feedback torque. Measured intervals remove that multiplicative error; they do not remove
encoder noise, which the ordinary filter addresses. This supports the user's proposed mechanism
for a mistimed derivative term in this model. It does not show that most robots have that
defect, establish robustness across plants, or test integral windup, timestamp uncertainty,
backlash, contacts, or a full PID implementation.

### Timing-contract prototype and independent audit

`experiments/timing_contract.py` is an exact-`Fraction` reference sink with no actuator API.
It takes an acquisition interval, position/velocity estimates and error bounds, and a
caller-supplied acceleration bound. It returns either an explicit invalid/expired status or
a predicted position center with radius

`position_error + velocity_error*maximum_age + |estimated_velocity|*clock_halfwidth
 + acceleration_bound*maximum_age²/2`.

The PM checked the formula against the source and the conditional Lean statement
`Research.TimingContracts.timed_prediction_error`. The root verified that theorem compiles
with only permitted axioms; the integrated build including it also passed. The triangle-inequality
argument is sound, but trajectory remainder, measurement bounds, and true clock enclosure
remain explicit physical assumptions. This is not closed-loop safety/passivity, and the Python
state machine is not formally refined against Lean. Exact rational arithmetic makes this a
transparent reference, not a hard-real-time 1 kHz implementation.

The PM found and reproduced two guard bugs: NaN sequence values bypassed ordering comparisons,
and epoch reuse `1→2→1` accepted old epoch-1 packets. The root repaired both. The PM inspected
the corrected source: counters require actual nonnegative integers, excluding booleans and
floats; resets require a strictly increasing epoch. The PM independently ran the timing-contract
and simulator regression files: all 12 tests passed in 0.03 seconds, including eight timing-contract
tests covering malformed counters, definite time reversal, and old-epoch rejection.
Overlapping acquisition intervals still cannot establish strict true-time
order. The later cumulative repair described below rejects intervals inconsistent with any
nondecreasing capture history, rather than checking only the last interval. Hidden physical-bound violations
remain undetectable in general, as the clock counterexample shows.

This is a practical outcome from the review process: the prototype now makes uncertainty and
stale-data rejection explicit, and independent tests closed two replay holes before any
hardware integration. It is an engineering reference with a conditional algebraic theorem,
not a newly invented timing method or a deployed middleware library.

### 01:30 checkpoint: reversal/reset integration audit

The PM checked saved hashes without rerunning Lean or the numerical batches. All ten files
listed in the problem-273 checkpoint and all eleven files in the vision checkpoint match;
the three frozen simulator-source hashes also match their result files. Earlier theorem and
simulation evidence therefore remains tied to the same saved sources and artifacts.

The source review identifies these integration boundaries for the bounded event replay:

- A signaled reset clears the sink's stored observation. It cannot revoke a previously
  returned `Prediction` object, which carries no epoch or sequence. A downstream consumer
  must re-query at application or use an external epoch/version check; caching a ready result
  across reset is not covered by the sink's current guard.
- `at(execution_time)` is a stateless estimator query. It permits decreasing query times;
  it does not enforce chronological command application. Both acquisition and execution
  times must use a consistent clock interpretation for the active epoch.
- A higher sequence with an overlapping acquisition interval is accepted only if the full
  accepted history still permits nondecreasing capture times. The cumulative guard rejects
  globally inconsistent histories. This does not establish strict ordering of unknown true
  capture times, although each prediction can still satisfy its own conditional bound.
- An interval spanning a smooth velocity reversal is valid when position and velocity error
  bounds refer to the same unknown capture instant and the acceleration/remainder bound holds
  over the entire capture-to-execution span. A finite-difference velocity error must include
  curvature/truncation error, not only encoder measurement noise.
- A velocity jump or acceleration beyond the supplied bound violates that model. Such a
  hidden violation may still return `ready` with an incorrect enclosure; an expected negative
  control must preserve this distinction rather than mislabel it as universally detectable.

The root produced a bounded exact analytic reversal/event replay, subsequently checked
independently by the PM below. It tests these assumptions and integration boundaries;
it supplies no physical or closed-loop guarantee.

The root then identified a concrete cumulative-ordering gap, which the PM independently
confirmed. With increasing sequences, intervals `[10,20]`, `[0,11]`, `[1,2]` pass the old
latest-only check, although the third must precede the first. The implemented repair retains the
maximum lower endpoint of **all** accepted intervals in the epoch, rejects a candidate whose
upper endpoint is below that value, and clears the value on reset. This is the correct
feasibility test: choosing each possible capture time as the running maximum of lower
endpoints produces a nondecreasing sequence whenever every check passes. It does not prove
the unknown actual capture times are ordered or strictly increasing. The repair is implemented:
rejected samples do not alter the retained value, reset clears it, and prediction intervals
remain conservative rather than being narrowed. The regression failed before the repair and
passes afterward; the timing-sink suite now has nine passing tests as reported by the root.

### Exact reversal/reset replay: completed independent check

The artifact folder is `work/vision/timing-replay/`, with source snapshots, result summary,
and valid/false-bound query traces. The trajectory is `q(t)=t−t³/3` on `[0,2]`, with
`v(t)=1−t²`: velocity reverses at `t=1`, acceleration is `−2t`, and jerk is `−2`.
Thus the supplied bound `A=4` is valid throughout. Samples arrive at a nominal 50 Hz with
2 ms clock halfwidth; queries are at 1 kHz. Variable delay, duplicate/reordered packets,
a blackout, age expiration, and a signaled epoch reset exercise the sink.

The PM verified both recorded SHA-256 values and that saved source files match the current
implementation. Using a separate exact-`Fraction` calculation, the PM recomputed every ready
row's analytic truth, estimate, radius, and age condition rather than trusting its `enclosed`
flag. All 2,001 query timestamps and status counts match the saved trace:

| Replay | Ready predictions | Enclosure failures | Other query outcomes |
| --- | ---: | ---: | --- |
| Valid `A=4` | 1,813 | 0 | 141 expired; 37 acquisition not definitely past; 10 no state |
| Deliberately false `A=0` | 1,813 | 120 | Same status counts; first miss at 0.684 s |

The false-bound misses still report `ready`: the sink does not know the physical bound is
wrong. This is a deliberate negative result, not a new detection guarantee. The source replay
also records 74 accepted observations, 105 duplicate/reorder rejections, and two wrong-epoch
rejections. After reset, re-querying returns no state and old packets are rejected, but a
previously returned immutable prediction remains usable as an object. Consumers must re-query
or check an external version before application.

For ordering, the PM wrote a separate reachable-set oracle rather than reusing the running
maximum implementation or the root's brute-force function. Across all 1,000 three-interval
chains on endpoints 0–3, all 3,000 decisions agree: 2,607 accepted and 393 rejected. Rejection
leaves both stored observation and ordering state unchanged; epoch reset clears both. This
finite oracle supports the guard repair alongside the simple general feasibility argument;
it is not a Lean proof of the Python state machine or a guarantee about hidden capture times.

One initial harness assertion failed because reset and immediate arrival of a new-epoch
observation occurred before the same query, producing no logged `no_state` query. The root
added a disclosed 10 ms delay to the first new-epoch packet to exercise that boundary. This
was a test-coverage fixture correction, not evidence that reset itself failed.

This replay uses exact analytic evaluation, so it requires no numerical step-convergence
claim. Clock intervals and measurement-error bounds come from synthetic ground truth; no
clock-calibration algorithm, automatic reset detector, actuator, or physical plant is tested.
It is reported separately from the **988 plant comparisons**, not added to their count.
The bounded research work and final routine checks are complete; this report is the authorized
07:30 delivery. A final docstring clarified the ordering assumption; source snapshots
and hashes were refreshed, with unchanged replay counts. The PM rechecked the refreshed hashes.

## Verification and handoff

At the morning delivery pass, all **10 problem-273 manifest entries and 14 vision manifest
entries match their saved hashes**, with no recorded-artifact drift. All five frozen source
hashes for the two numerical batches and analytic replay also match. Result counts and
negative controls are unchanged. No build, test suite, or experiment was rerun during this
delivery check, and no concurrent work was overwritten. The problem-273 manifest retains an
earlier 164-test/lint snapshot; the later vision checkpoint and the report below use the
recorded 201-test run. These are dated checkpoints, not conflicting fresh measurements.

Latest root-reported Python checkpoint after the 01:30 work: **201 tests passed, one deselected,
in 7.77 seconds**. The concurrent suite has expanded since the earlier 164-test checkpoint.
Its total runtime exceeds the repository's approximately five-second target; the nine
timing-sink tests take 0.03 seconds. The three changed Python files pass targeted Ruff and
formatting checks. Whole-tree Ruff now reports one finding in concurrent
`tests/test_skew_normal_form.py`, and formatting flags eight files; the earlier 1,054/110
snapshot is superseded. Unrelated files remain untouched, and a clean whole-tree result is
not claimed.
The final focused sink/simulator run passed all 13 tests in 0.02 seconds as reported by the root.
Other agents' files are preserved. Final theorem direct compilation, axiom audit, and statement
review pass. The integrated build passes with 8,973 jobs. All six visual-reference and eight
direct-feedback convergence checks pass. The freshness method fails its advancement gate;
known timestamp/filter corrections pass the specified direct-feedback comparisons. Hardware
and broader experimental validation remain outside this completed checkpoint. Reproduction
instructions are saved in `work/vision/reproduce.md`.

The PM also inspected `tremor-summary.png`: it distinguishes direct feedback from visual-target
reconstruction, labels the logarithmic jerk scales and seed ranges, and states that the
experiments are synthetic, established-method comparisons rather than hardware or novelty claims.

The final `ctrl check --all` rerun exits 3 solely because 834 is `NOT_APPROVED`; its build,
token/axiom audits, and exact statement binding pass. Problem 273 is skipped as a challenge solution
because no approved full-problem solution exists. Challenge files are unchanged.

The existing 834 result remains subject to its human approval gate. Seven-smooth partial
progress would not solve Erdős 273. No publication, outreach, new credit purchase, hardware
connection, or controller deployment is implied by this report.

Two useful next requests, depending on priority:

- Mathematics: “Extend the completed seven-smooth proof to the eleven-smooth computational
  certificate, independently audit its statement, and check the specific restriction against
  prior work. Explain any remaining gap without repeating the completed seven-smooth proof.”
- Robotics: “Validate the timing prototype offline against recorded robot telemetry with
  documented provenance, units, acquisition/receipt/application timestamps, and command
  semantics. Test cached-prediction invalidation and clock resets at the consumer boundary;
  compare with correctly timestamped filters and Ruckig at matched lag. Report negative
  results and model violations. Hardware control requires a separately defined scope.”
