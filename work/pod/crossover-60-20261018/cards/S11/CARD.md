# S11: Travel containment versus maintained rest

**PM: GO for a transient-to-terminal contract; complete precision-stop guarantee remains HOLD.** AI-written. Root PM, domain researcher, inventor and independent critic used inherited root models; exact runtime identifiers unavailable. Role diversity is not model-family diversity. Actual substantive timing and excluded context gaps are in state/activity.

Original question: What additional controller and contract are needed to guarantee two-sided travel and explicit residual-motion tolerances after the finite first-zero maneuver?

The frozen sources are C8 constructed-handoff-08/REPORT.txt, milestone-01/REPORT.txt and adjacent-controls/adjacency-review/performance-level-review.txt; full paths and hashes are in roster.json. Actual C5/C7/C8 definitions were inspected. This was investigated prior work. C8 gives a finite forward ceiling; campaign S01 separately supplied an infinite extension of the unchanged law. Neither establishes two-sided precision rest.

## Findings that change the next experiment

The plant is x'=v,v'=a,a'=r(b-a), r in[8,12]. Hold feedback is clipped -8(x-c)-6v-a/2, clip±2, then target error±.01. Sensor errors are(1mm,.01m/s,.05m/s²), total age≤1ms. C6 has only an UPPER initial-position bound. An absolute lower travel guarantee for the full maneuver therefore requires a lower initial-position assumption and prefix proof, regardless of the later controller.

The source weighted box uses z=(x-c,x-c+v/4,x-c+v/2+a/16), weights(1.02,1.01,1). At K=.045 it guarantees |v|≤.3654m/s and |a|≤2.9088m/s²: bounded motion, not precision rest. A contract must specify position limits, velocity/acceleration tolerances, deadline, hold horizon and the same execution/history. The illustrative1mm/s target below is a test specification, not an original requirement attributed to the source.

At ACTUAL reading632, m=(10051/156250,27/2500,-6/5), the third propagated observation interval requires c≤K-.01569643. Certifying x≥0 with this box requires c≥1.02K. Lean proves incompatibility for EVERY K≥0. Changing only center/radius cannot repair this certificate at that event. This does not prove actual negative travel or exclude a tighter reachable set.

The old braking polynomial reaches v=0 at t=.325 with a=-1.2. Continuing it gives x(2/3)=-17/3000. Switching only to effective target0 leaves negative actuator memory and eventual backward drift. These are policy diagnostics, not the actual C8 hold trajectory, which switched at.3165.

A stronger necessary reserve uses actuator limits: from v=0,a=-1.2, b≤2.01,r≤12, comparison gives a(t)≤2.01-3.21exp(-12t). At t=1/12, displacement≤2.01/288-3.21exp(-1)/144< -1923/1600000m. At least **1.201875mm of backward reserve** is necessary for this state even with favorable allowed input. The differential comparison/integration are hand-derived; Lean checks supporting boundary and arithmetic lemmas, not the full trajectory theorem. This first-zero state is not the positive-speed actual C8 arrival. Earlier weaker .388195/.776390mm bounds are preserved.

## Three transfers and their breaking points

1. Viability and robust optimization → terminal admission. Intersect original propagated observation intervals with center reserve[L+1.02K,U-1.02K]. Exact existence is a maximum-lower-endpoint test. It preserves actual source coordinates. It breaks if a changed center is substituted into the old assembly without rebuilding future commands, or the lower prefix/history is omitted.
2. Actuator memory → stopping momentum. For constant r, p=v+a/r satisfies p'=b. Zero velocity can carry hidden actuator momentum. This unexpected representation explains release-at-zero failure and suggests a nonlinear clearance boundary. Its unchanged identity fails for variable r; the retreat comparison instead uses actual rate bounds.
3. Temporal contracts and signal norms → maintained-motion predicates. Replace a first-zero event or observed dwell by an all-future or finite-horizon tolerance on the same execution. Signed convolution kernels tighten residual estimates. Fixed-rate assumptions and asymptotic bounds cannot silently become arbitrary-rate deadline guarantees.

## Discriminating tests and independent critique

Root retained the original braking prefix: sigma=.316, arrival=.3165, center=.02525673, first command=.22264264. Future readings are exact; r8; target error alternates±.01 in one-second blocks, constant on each .5ms cell. These are permitted future C7 streams, distinct from the literal saved three-cell witness.

pm_interval_hold.py encloses exp(-1/250) with exact Taylor bounds and propagates21,000 cells with outward integer intervals, retaining current and previous physical states. Every command is inside clipping. At global time21633/2000=10.8165s, velocity is enclosed around **.0022881462917086763m/s**, strictly above.001. Critic independently used physical-coordinate scalar flows, positive-exponential-series inversion and another precision; inventor independently repeated it. All agree. This is exact Python arithmetic with reviewed analytic/source binding, not a Lean certificate of the execution.

Numerical80s continuations show late peak speeds2.314764mm/s at r8 and2.109406mm/s at r12; sampled positions stay positive. These are numerical observations, not continuous safety certificates or proof that this actual C8 continuation never settles. The finite exact witness rejects a≤1mm/s requirement starting by that time. A separate symbolic period-two terminal-history construction permits indefinite nonzero motion, but its initialization is not proved reachable from C8 entry.

Negative controls: current-sample substitution and acceleration reset change the exact late state, although both still exceed the coarse threshold. Threshold-only acceptance therefore misses binding errors. Inventor found a prototype non-grid duration was silently floored; root added an explicit rejection guard and reran the unchanged grid-aligned witness. Failed interval formulas losing algebraic dependency remain saved as enclosure failures, not physical counterexamples.

## Positive candidate and explicit new assumptions

Retain feedback gains; choose K=1/8120. Then V=.001m/s,A=202/25375≈.00796059m/s²,X≈.125616mm. The prospective contract requires target error≤.0001, sensor errors(1µm,10µm/s,.0001m/s²), age≤.5ms, and retained sample history inside the same box with a justified derivative bound. These are stronger specifications, not measured hardware facts or the original source assumptions.

Exact refined residual30174381/101500000000<.0003. Lean verifies all SIX actual transformed-field faces inward for r∈[8,12],|w|≤.0003. Full digital first-exit, settling path, history flush, initial lower clearance and any changed-center construction remain open.

A separate fixed-r8 hand derivation retains original error/age bounds. Signed command-derivative kernel gives C=8+24exp(-4)<76/9 and conditional limsup|v|≤251217/8924000≈.028150717m/s. This improves the old box estimate but provides neither1mm/s nor a deadline. Convolution, calculus and fading-memory bridges are unformalized; exact auxiliary bounds are saved in domain_gain_note.md and its executable check.

## Evidence and decision

Source-bound terminal algebra, actual-reading obstruction, inward faces and retreat arithmetic compile independently using only propext,Classical.choice,Quot.sound. Final counts/hashes are in pm_kernel_acceptance.json and role logs; existing pinned C8 dependency objects were reused, not fully rebuilt. No approved Challenge, original source, public CLI or physical robot changed. No novelty or standards-compliance claim.

GO after all60 initial reviews:30minutes on finite settling plus retained-history admission, with the one-sided retreat comparison formalized. Test20 predeclared semantic mutations, require one source-bound positive and independently rejected changes. HOLD complete precision-stop guarantees until lower clearance, tolerances/deadline, physical precision and entry/history premises are justified. NO-GO for firstzero-as-rest, history reset, or merely shrinking the old box under unchanged errors.

Quality: faithfulness4,reproducibility4,discrimination4,critique4,actionability3 = **95/100**. This grades the review, not proof completion. Subjective confidence is high for scoped algebra and the finite witness; full controller feasibility and physical applicability remain unresolved, without a calibrated probability.

Final comparison check: retaining actual arrival velocity .0102 adds .00085m to the first-zero comparison at1/12s. The same hand bridge therefore gives actual-arrival displacement≤−563/1600000m=−.351875mm. This is not a lower-limit0 violation; that arrival has ample position clearance. Exact input/output fractions are in pm_arrival_retreat.json.
