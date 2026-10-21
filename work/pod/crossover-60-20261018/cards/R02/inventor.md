# R02 inventor — execution traces, not sampled jets alone

AI-written inventor contribution; inherited root model, exact identifier unavailable.
Original question: preserve the actual native trajectory jet across repeated replacements,
and retain all real jump contributions. Source native-execution-06/builder/report.txt and
make_references.py/run_comparison.py were inspected read-only. The repair carries actual
native C++ q/v/a into each new native plan, with binary execution origins and cumulative
phase boundaries. It does not claim jerk continuity, global exact C2 polynomial joins,
continuous-runtime equivalence, firmware identity, or hardware validation.

## Three distinct transfers

1. **Verified compiler trace refinement.** Treat native trajectories, the exported exact-cut
polynomial schedule, and the plant event stream as three intermediate representations.
The refinement relation must preserve native replacement input, execution origin, retained
state, event support, one-sided reference jets and which plan actually owns every interval.
Finite q/v/a agreement is one observable, not the entire semantics. Source-native at_time
subtraction must not silently be replaced by subtraction on the rational scheduler clock.
A useful next certificate binds each executed piece to its originating plan and exact binary
cumulative cuts; clipped plan validity ends at the next real commit. Falsifier: a phase
that was superseded before execution contributes a physical interval or a TV jump, or
polynomial replay state is supplied as the next native initial state. This is a concrete
translation-validation route, not a proof of the native planner's internal algorithm.

2. **Distributional derivatives and bounded-variation accounting.** A command jump is an
atom of its derivative measure. Under the source direct controller and continuous physical
state, its weight is exactly 800Δq+60Δqv+(3/2)Δqa+Δj/96. Total variation sums absolute
atomic weights separately from the continuous contribution. Two distinct cuts can have
opposite atoms that cancel algebraically but still contribute positive variation. A short
interval's small displacement cannot justify removing those atoms. Falsifier: converting
exact cuts to display floats merges our live fixture and reduces its jump TV by about.3125.
The physical clock remains the exported cumulative clock; positive local-duration metadata
with coincident cumulative endpoints does not itself create a physical interval. Likewise,
superseded metadata is not executed support. At a genuinely single execution cut, the
actual left/right command defines the jump; merely listing extra zero-duration internal
records must not manufacture multiple physical jumps.

3. **Unexpected transfer: information-theoretic completeness of verification observations.**
A finite jet-query oracle cannot distinguish every execution trace in the larger class of
bounded-jerk piecewise-cubic references. Build a compact pulse with zero first three jerk
moments: four equal-width jerk phases J[1,-3,3,-1]. Integrated q/v/a return exactly to rest,
without a reset, and the trace agrees with rest outside the pulse. Put it between query
instants: every recorded q/v/a sample can agree while command-jump variation differs.
This is the same structural distinction as unobserved intent or hidden-state ambiguity:
the observation map is not injective for the property being certified. Falsifier for an
acceptance adapter: it accepts the all-rest replacement solely because all finite q/v/a
samples agree, despite dropping the pulse's event certificate. This diagnostic is not
claimed to be an output of Ruckig; it shows what additional source-bound event semantics
are needed before finite native test evidence can be generalized.

## Exact source-data test

`inventor_tiny.py/json` reads only frozen06 reference-schedules.json and records its SHA256.
It treats saved binary64 coefficients as exact rationals and uses the exact exported cuts;
this is an exact polynomial interpretation, not bit-identical native at_time evaluation.
There are11 executed Ruckig pieces with width≤1ns;9 have equal rounded absolute float
endpoints. The strongest selected live witness is hold_jitter / ruckig /
plan_29_main_0:

- start=3602879701896397/4503599627370496,
- end=461168601842738819/576460752303423488,
- width=3/576460752303423488 seconds (about5.20417e-18),
- jerk jumps -15 then+15,
- exact two-jump command TV about.31250000000000006.

Combining the two jump weights before taking the absolute value loses essentially the
whole.3125 contribution. The JSON retains exact fractions, neighbouring one-sided jets,
and the reference's retained changes over the interval. This is a jump-only accounting
negative: continuous command variation is still required separately, and the exact
source physical-state trajectory was not rerun here. At each actual boundary physical
state cancels from the jump formula; no physical reset is inserted.

## Exact hidden-observation test

`inventor_hidden.py/json` uses J=5/2, phase width1/10000s, start3331/10000s. Its four
jerks are2.5,-7.5,7.5,-2.5, respecting the source's7.5 maximum absolute jerk value.
The zeroth, first and second jerk moments vanish exactly. All1001 q/v/a samples on
the1ms grid over[0,1] coincide with all-rest; q/v/a return to zero through integration.
Yet jerk jump TV is40 and command-jump TV is5/12 in the source controller's units.
The interior acceleration is nonzero. No finite snap bound is claimed at the jerk jumps.
This is a deliberately changed diagnostic reference, not a new native-plan test case.

`inventor_hidden.lean` proves the four exact polynomial phases return to rest for arbitrary
J,h; the first phase is nontrivial for positiveJ,h; jerk jump variation is16J for J≥0;
and the concrete command-jump value is5/12. This scalar proof does not formalize all
continuous-time traces or native Ruckig. Its initial compile required marking real-valued
helper definitions noncomputable; that failed log is preserved separately. Final compile
and axiom output are in inventor_hidden.log.

## Proposed decision and precise next test

GO for a bounded translation-validation consumer, preserving the source's actual clock and
retained native initial states. Require a complete executed-piece partition, origin/phase
binding, actual one-sided jets, and separate continuous/jump metric contributions. Replay
both negative controls: omit the live tiny piece and add the superseded coincident-endpoint
metadata as fake support. Also reject replacement using scheduler-time or replay-state
inputs. A sampled q/v/a oracle alone is NO-GO for event/variation completeness. A calibrated
firmware/runtime guarantee remains HOLD on its execution and arithmetic contracts.

Evidence: exact rational saved-data replay, exact changed-reference diagnostic, small kernel
algebra; no physical experiment, general native equivalence theorem, or energy-in-joules claim.
Quality18/20 (faithfulness4,reproducibility4,discrimination4,critique3,actionability3).
Subjective confidence98% in isolated algebra, not a calibrated hardware probability.

Final kernel status: exit0, all four declarations use only propext, Classical.choice,
Quot.sound. Frozen SHA256 e64ee9cb78e4e1c8411c7270f2e35e5fbe68ecbbf97608b0d8654cd864231e0c.
The independent critic reproduced the nine live float-endpoint collisions and the selected
.3125 command-jump loss. Domain independently checked the four-phase algebra; its independent
compile and the critic's hidden-pulse replay are separate evidence owned by those roles.
