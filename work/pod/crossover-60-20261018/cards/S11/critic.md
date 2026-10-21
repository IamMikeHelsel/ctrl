# S11 independent critic

## Recommendation

GO for an explicit two-sided transient/terminal contract and a certified settling-to-terminal-set construction. HOLD the complete stopping claim: original C8 proves a forward ceiling, not the newly requested lower travel and residual-motion tolerances. NO-GO for replacing maintained rest by first velocity zero, or declaring a narrower hold box invariant without checking its disturbance budget and actual entry.

A complete proposed contract must name absolute or relative travel, both travel limits, a stopped predicate (at least speed and acceleration tolerances), attainment deadline, required hold duration, disturbance/fault/energy assumptions, and the physical/controller history retained at switching. Rejection of a terminal-set admission is not itself a safe fallback: continued braking can reverse travel.

## Owning-source audit

Read the frozen C8/C1 reports, performance-level review, and actual DigitalHold, ClearancePolicy, WeightedEntry, and DetectorBridge sources. C8's current gains are (-8,-6,-1/2), command is clipped to[-2,2], target error is bounded by.01, rates lie[8,12], sensor errors are(.001,.01,.05), total information age is at most1ms. C5 guard uses m_x<=.143 and has no lower position condition. More fundamentally, C6 initial position only satisfies x0<=.001; there is no initial lower bound. Translating an admitted input arbitrarily left preserves the dynamics, guard, and translated policy center. No uniform absolute lower position claim can follow without an initial lower bound or an explicitly relative-travel contract.

C1 permits an initial zero velocity followed by positive acceleration; that witness shows first-zero semantics, but is not a C6 initial condition because C6 requires v0>=.39. The actual C8 witness switches at .3165, before the old braking path's first zero .325. Counterfactual continued braking after .325 is not the actual C8 hold continuation.

Campaign S01 already constructs an infinite coherent extension of the ORIGINAL hold law under its stream assumptions. Do not list that original existence problem as wholly untouched. A new center/controller, tighter error contract, or terminal policy still needs its own entry, execution, and history binding; S01 does not automatically transfer.

## Independent exact and numerical evidence

`critic_exact.py` reconstructs original rational policy arithmetic without producer imports. The old polynomial first zero is t13/40, state(103/1600,0,-6/5). Continuing old braking for only.5ms moves backward3/20000000m and yields v=-3/5000. Replacing the effective target by zero, without resetting acceleration, yields v(1)<-.149m/s and more than.13m backward relative travel. These are explicitly changed-mode diagnostics.

At true rest with exact reading and u=0, the admitted next-cell disturbance d=.01 and rate8 gives a=.01(1-exp(-8t)), v=.01[t-(1-exp(-8t))/8]. Exact rational exponential enclosures prove positive acceleration, velocity, and travel at h=.0005. Thus arbitrary unmeasured error changes do not preserve exact rest. This is a hold-law terminal-state test, not C8 guard reachability.

Allowed constant sensor errors(.001,.01,.05) and target error+.01 also admit a stationary equilibrium x-c=-83/8000=-.010375m, with command-.01 and no clipping. This equilibrium lies in the hold cube but is not asserted reachable from the guard. With exact readings, inventor's simpler stationary offsets±1/800 under d=±.01 were independently checked.

The weighted plateau K=.045 gives only |x-c|<=.0459m, |v|<=.3654m/s, |a|<=2.9088m/s². Independently enumerated all eight vertices and checked inventor's policy/source hashes. These are sharp bounds for the abstract box, not necessarily attained trajectory extrema.

For the ACTUAL first C8 reading m=(10051/156250,27/2500,-6/5), the original center is.02525673 and box interval[-.02064327,.07115673]. More strongly, every candidate center/radius in this weighted measurement-box family fails the lower travel requirement x>=0: its third coordinate requires c<=K-.01569643, whereas lower reserve needs c>=1.02K. These are inconsistent for all K>=0. This is certificate-family infeasibility, not proof that the actual trajectory crosses zero.

`critic_sampled.py` independently reconstructs the actual C8 prefix and delayed control using scalar exp/expm1 held-flow formulas, no matrix exponential or producer imports. Sample clock is .316+n*.0005, and that reading commands the cell starting .316+(n+1)*.0005. It preserves the pending state at .3165 and verifies first command.22264264. With zero future sensor errors and target error alternating±.01 in1-second blocks, 80-second numerical results match root to below5e-16 in compared statistics. Tail sampled speed peaks are.00231476416456m/s (r8) and.00210940561443m/s (r12). These are numerical observations, not continuous or infinite-time certification.

`critic_interval.py` supplies a separate EXACT late witness for r8: at absolute time21633/2000=10.8165s (10.5s after arrival), v is enclosed in an interval of width<1.12e-50 around.0022881462917086763m/s, strictly above1mm/s. It uses physical coordinates, independent positive-exponential-series inversion, 80-digit outward rounding, and verifies clipping inactive on all21000 cells. Its interval overlaps root's independent centered six-state calculation. The first draft used b+(a-b)E naively and lost interval cancellation, causing excessive enclosure width; preserved as critic_interval_dependency_failed.py.txt, then algebraically expanded before acceptance. It was not a physical clipping failure.

One finite witness refutes a residual-speed requirement already in force at that time. It does NOT prove this actual C8 continuation never eventually settles. A separate exact hand-derived period-two history (`critic_periodic.md`) gives bounded nonzero motion for the same sampled feedback, with rationally checked |delta|≈.00500501<.01 and inactive clipping. Its terminal delayed history is initialized on the orbit, not proven reachable from C8. Its tiny speed does not violate a1mm/s tolerance; it demonstrates the difference between bounded motion and exact rest.

## Additional control/contract implications

The domain's exact interval-intersection test correctly expresses existence of a center whose propagated observation box fits BOTH travel reserves. It is an admission criterion, not a proof that the original C8 command, which uses its original center, follows the new center. Any changed center must be bound to actual future commands and unchanged state/history.

At the r12 third upper weighted face, derivative=-1.9K+.75W. Inwardness with the proposed1mm/s box requires W<=19/60900≈.000312m/s², below the original physical error.01 before sensing/age contributions. This rules out that full-box residual certificate under original error bounds; it is not an impossibility theorem for all terminal sets or controllers.

The small-box arithmetic/faces use explicitly stronger sensors, target error and age, with K1/8120. Their favorable budget is a prospective contract and still requires actual terminal entry, history containment, first-contact/bootstrap, and execution construction. A finite transient tube followed by terminal admission is a discriminating next test, especially because the actual C8 entry does not fit any nonnegative-travel box of the proposed family.

Inventor's retreat comparison is valid without assuming actual acceleration stays above its initial value: on the upper affine barrier, r(b-a_bar)<=12(B+A). With A1.2,B2.01, jerk slope38.52, integrating gives x-x0<=-.6t²+6.42t³. At t20/321 this yields retreat at least80/103041m≈.77639mm, twice the initial10/321 witness. The differential comparison/integration bridge remains hand-derived; source C8 switches before this zero-speed/negative-acceleration state.

## Evidence limits and next gate

Twenty-one declarations independently compiled with only permitted axioms: terminal6, face4, obstruction2, small_budget2, small_faces1, inventor retreat6. Independent Lean replays and hashes are in critic_* logs/JSON. The source-importing domain modules prove conditional algebra, box admission, face inequalities, and source-specific obstructions. They do not prove the complete new stopping controller or the Python trajectory witnesses. Existing pinned source dependencies were reused; this critic did not rebuild the entire C8 import graph. No physical, PL/PFH, loss-of-power, brake, or robot result is inferred.

Twenty proposed semantic mutation tests are in critic_next_gate.json, not an executed30-minute extension. Source-approved files are unchanged. Scoped Python lint and formatting were checked. Quality grade A- for source binding and independent discrimination; complete two-sided stopping/precision-rest implementation remains HOLD. Grades are subjective rubric judgments, not calibrated probabilities.

Final card audit: accepted scope and numerical statements. Independently recompiled the sixth retreat arithmetic lemma and checked exp(-1)>367/1000 with a rational enclosure. The stronger exponential barrier gives displacement at1/12s less than -1923/1600000m (1.201875mm retreat); comparison/integration remain hand-derived. Root's new non-grid/negative-duration rejection guard leaves the default late-witness certificate exactly identical; both invalid-duration controls reject. See critic_final_audit.json.
