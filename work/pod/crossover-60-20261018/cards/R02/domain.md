# R02 domain — retained native jets and event-aware command variation

AI-written; inherited root model, exact model identifier unavailable. Original sources were inspected read-only. This review adds no hardware result, native library patch, changed plant/controller, or new benchmark case.

## Frozen question and strongest prior result

Can the execution adapter preserve the actual native trajectory jet across repeated replacements and retain every real jump contribution in its metrics? The source native-execution-06 report already records a successful finite fidelity repair of05 and a fixed144-case scalar plant batch. It explicitly preserves05's failed native-clock gate. The original native API state is position, velocity and acceleration, not a jerk-continuity condition. Native carry, exact-real polynomial interpretation, floating-point evaluation, actual plant state, and physical firmware fidelity are distinct claims.

The primary [Ruckig documentation](https://docs.ruckig.com/) describes state-to-state generation with velocity, acceleration and jerk limits. This supports the API framing, not an added guarantee that repeated replacements preserve jerk or that our local export is bit-perfect. The inspected local pinned source, not the current online version, determines this experiment.

## Actual implementation and clock semantics

`native_execution.cpp` retains the previous C++ trajectory. On the next accepted commit it calls `trajectory.at_time(current_double_commit - previous_double_commit,p,v,a)`, then uses those native values as the next plan's input. It rejects nonincreasing native commits. No polynomial replay or plant state enters the native replan. Limits remain speed0.1, acceleration0.5, jerk7.5, optional minimum duration0.8.

`profile_export.hpp` serializes round-trip doubles, main cumulative boundaries, local durations, phase initial jets and native samples. These are different fields: a positive local duration can have coincident cumulative endpoints. `make_references.py` assigns the physical polynomial origin the exact rational value of the native binary commit, and adds the exported cumulative boundary exactly. It clips each executed phase at replacement time. Positive but zero-measure or superseded phases stay metadata and must not manufacture executed intervals. Scheduler rational times remain provenance, not substitute origins.

`run_comparison.py` carries actual x/v/a through every event. At each boundary it evaluates both reference sides while using the same actual state. Its source command is

    u=−800x−60v−0.5a+800q+60q'+1.5q''+q'''/96.

Therefore Δu=800Δq+60Δq'+1.5Δq''+Δq'''/96, and actual jerk changes by rate×Δu if rate, disturbance and actual acceleration remain the same. A state reset introduces the additional terms−800Δx−60Δv−0.5Δa. The symbols q',q'',q''' here denote exported within-phase derivative fields. Nonzero position/velocity joins prevent treating them as global classical derivatives; distributional derivatives would also contain impulses. The source controller uses the exported fields directly. The source keeps command continuous variation and jump mass separate. Its continuous integral and squared-jerk integral are numerical quadrature, not exact integral certificates or joules.

## Independent exact saved-artifact audit

`domain_audit.py` imports no source producer. It reads all12 native histories,492 plans and480 replacements. Each next current-state tuple equals the previous saved native sample at exactly the saved native elapsed time. This is independently checked saved-artifact consistency, not a fresh C++ or firmware execution. `domain_subtraction.py/json` additionally checks all480 elapsed-time differences against the exact rational difference of their two binary commit values: all480 are exact, and all480 satisfy the positive Sterbenz ratio condition previous/2≤next≤2previous. No subtraction-rounding allowance is needed for these480 replacements. This is a finite assertion; arbitrary more widely separated commits may round. Scheduler-to-binary-origin rounding and later intra-trajectory arithmetic remain separate issues.

For all12 native reference schedules it evaluates every adjacent piece endpoint over Fractions, interpreting each serialized binary coefficient as an exact rational. All boundary times join exactly. It retains all862 nonzero position/velocity/acceleration joins rather than asserting global C2. Maximum magnitudes across schedules are approximately1.861e−18m,5.296e−18m/s,3.855e−16m/s². These tiny nonzero joins are consistent with the source's explicit limitation.

The exact-real jump ledger computes the command mass at every executed boundary. Per-schedule jump TV ranges from approximately0.46875 to18.4375m/s². These are jump contributions only, not total command variation. The JSON stores every signed jump and its exact time, both phase origins, and exact rational mass. The source numerical plant simulation is not rerun here.

A useful quantitative bridge is

    | |Δu|−|Δj/96| | ≤800|Δq|+60|Δq'|+1.5|Δq''|.

Summing it bounds the error incurred by simplifying the full boundary command formula to its jerk term. Across these12 histories the largest such summed bound is6.894e−15m/s². A per-join fidelity tolerance alone cannot bound total variation for an unbounded replacement stream: the summed bound scales with the event count and must remain a ledger or explicit cumulative budget. Thus finite differences like the source's0.625 change in command TV cannot be explained by neglecting these q/v/a rounding joins; the changed jerk-side/event structure matters. The saved exact ledger still retains them. This does not certify the numerical continuous-TV quadrature.

## Crossover and proof boundary

The useful transfer is from hybrid-system event accounting and bounded-variation measures: per-plan smoothness is insufficient, and a jump is an atom whose mass is its absolute change, independent of the neighboring interval's duration. Inventor's live tiny-phase fixture and vanishing-duration pulse supply independent negative tests. Opposite jumps cancel in signed endpoint displacement but add in TV. A zero-measure metadata phase, however, is not an executed positive-duration pulse and must not add an invented pair of atoms.

`domain_jumps.lean` checks the literal source command jump, extra reset terms, actual jerk jump under fixed rate/disturbance/state, weighted residual bound, reverse-triangle jump-mass bound, and elementary positive-ledger omission facts. These are conditional real algebra; they do not certify C++ floating arithmetic, event completeness, or a whole physical trajectory. Failed producer attempts remain logged. Acceptance requires exit0 and permitted axioms, independently replayed.

GO: independently consumed, model-bound event ledger with complete native carry provenance. HOLD: a continuous native-to-polynomial fidelity theorem, certified continuous-TV quadrature, timestamp-to-firmware transport, or arbitrary industrial execution. A useful next bounded test mutates the clock origin, replaces cumulative times by duration sums, deletes tiny live phases, treats superseded metadata as executed, or resets plant state, and requires rejection against a frozen event/carry contract. No new native interpolation algorithm or energy-saving result is claimed.

Quality18/20(90%); subjective confidence high in the exact saved-artifact identities, limited for continuous native and physical execution beyond those hypotheses.
