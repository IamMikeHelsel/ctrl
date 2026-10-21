# R02: Reference continuity across native replanning

**GO — quality95/100, not a probability.**

Question: Can an execution adapter preserve the actual native trajectory jet across repeated replacements and retain all real jump contributions in its metrics?

Prior work: Native execution repair retains C++ trajectory state and reports finite reconstruction tests; tiny joins and jerk-side differences remain explicit.

Original obstacle: Finite sampled agreement is not continuous-runtime or firmware correctness; clock rounding and zero-duration metadata matter.

Sources:

- /Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/native-execution-06/builder/report.txt
- /Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/intent-contract-07/analyst/industrial-comparison-addendum.md

# R02 program-manager review

AI-written four-role pod. Root PM, inventory_math domain, inventory_vision_robotics inventor, inventory_controls_safety critic; all inherit root model, exact runtime identifier unavailable. No alternate-family or Spark inference. Frozen original question: Can an execution adapter preserve the actual native trajectory jet across repeated replacements and retain all real jump contributions in its metrics?

Sources: native-execution-06/builder/report.txt and intent-contract-07/analyst/industrial-comparison-addendum.md in the notebook robot-motion pods, hashes unchanged. Read native_execution.cpp, native_replay.cpp, profile_export.hpp, make_references.py, run_comparison.py, and pinned Ruckig trajectory.hpp at revision99751e6ebc7c963bb80e99fbbe66f2c279d1db57. Official https://docs.ruckig.com/tutorial.html confirms state carry through pass_to_input and states minimum duration is not a general exact-duration guarantee. This review uses the pinned local implementation, not an assumption that current documentation proves its behavior. No proprietary industrial interpolation claim.

The original06 repair retains actual C++ trajectory q/v/a across replans. It does not carry jerk as a continuity constraint. Physical reference cuts are exact rational binary commit plus exact binary exported cumulative boundaries, not the rational scheduler clock or a sum of local durations. These are explicit exported-polynomial semantics, not bit-identical native evaluation or firmware. Raw/FIR history, original plant batch, reference limits and prior failed05 gate remain unchanged.

## Tests and lessons

Domain independently checks492 saved plans,480 native q/v/a carries, and all12 executed native-reference histories. Every replacement elapsed subtraction equals the exact rational difference of its binary commits in this batch; all satisfy a sufficient Sterbenz ratio. This is not a universal subtraction claim.862 tiny nonzero q/v/a joins remain explicit; their aggregate contribution differs from jerk-only jump accounting by less than6.894e-15 in the largest history. These exported fields are within-piece derivatives, not global classical derivatives through the joins.

Critic independently compares84,316 saved native queries against exact binary-coefficient polynomial evaluation. Original q/v/a tolerances pass, but six jerk-side mismatches persist. Root reimplements pinned native branch selection, and critic independently scans those branches; all84,316 native jerk outputs match. Five persistent-goal queries have local subtraction error+2^-55, exactly the remaining physical phase width, and cross a native branch boundary. The sixth seeded case has exact local subtraction, but exported tail start exceeds total native duration by2^-53. These query-time cases do not contradict exact480 replacement subtractions.

Root also freshly executed the unchanged saved native_replay binary, SHA b980af6030be82ea6596eca6d4580791e8fe1e3f2dc9595c4e6528f54ee7ce89, on all12 original inputs. Every full output JSON matches the saved native data (84,316queries). Outputs are isolated in this campaign; no new native build, plant batch, input case, dependency, hardware or source change. This is fresh finite native execution, not a continuous-time or firmware theorem.

There are11 executed reference intervals≤1ns, nine with distinct exact endpoints that have the same rounded absolute float. A live hold_jitter piece of width≈5.20417e-18 contributes approximately.3125 to its two adjacent command-jump magnitudes. Across full histories, grouping signed atoms by rounded timestamp loses up to1.25m/s² jump variation. The current source does not perform that faulty merge. The different positive-local-duration2^-58 phase with coincident cumulative endpoints is superseded before execution; metadata retention must not invent a physical interval or jump excursion.

## Three transfers

1. Verified-compiler trace refinement. Preserve original/native/physical clock representations, native plan ownership, source bytes, branch conditions and both event sides. Query agreement alone cannot establish refinement. New interval guard lemmas prove a branch side only when the entire clock-error interval clears the cut; otherwise preserve both candidate sided jets. Clock-error bounds for actual compiled operations are a separate obligation.
2. Bounded-variation/distributional bookkeeping. Command jump at fixed actual state is exactly800Δq+60Δv+1.5Δa+Δj/96. Different exact cuts require separate atoms even if printed float times coincide. At one genuinely equal execution cut, zero-duration metadata is collapsed to the physical left/right change. Include endpoint/initial-atom convention. Continuous variation remains separately integrated; jump-only accounting is not total variation.
3. Information-theoretic adequacy of observations. Inventor's four equal-width jerk phases (5/2)[1,-3,3,-1] return exactly to q=v=a=0 without a reset. At width.0001 beginning.3331, all1001 one-millisecond q/v/a queries equal an all-rest trace, but reference-command jump variation is5/12. A family can fit in any finite observation gap and have arbitrarily small reference squared-jerk integral125h while retaining that jump variation. Root kernel-checks state composition, source jump algebra and constants; placement in an arbitrary finite gap and continuous derivative interpretation are hand bridges. This is a diagnostic piecewise-cubic class, not a claim Ruckig emits the pulse. Reference squared jerk is neither actual plant jerk energy nor physical joules.

Root's separate three-phase rest-to-rest pulse ends at q=2Jh³,v=a=0 with finite jump variation; it complements the stronger zero-displacement four-phase example. Failed Lean development logs are retained and excluded. No forbidden axiom is accepted.

## Decision

GO95 for a typed, source-bound executed-event/branch certificate. Literal all-time full native-jet equality of the present polynomial adapter is not established and is refuted at six saved jerk queries; firmware remains HOLD. The next experiment must preserve this distinction rather than silently weakening equality to sampled q/v/a tolerance.

After all60 initial reviews, spend30minutes on one manifest-bound native binary64 branch contract and one explicit exported-polynomial event contract. Predeclare20 controls, require independently checked branch/decomposition/carry evidence and retain all executed atoms. Quantify cumulative jump-error budget rather than only a maximum per-join tolerance. A practical common certificate may expose an ambiguity interval at boundaries instead of inventing exact native/physical identity. No public integration or hardware.

Quality4/4/4/4/3=95/100. Subjective confidence high for scoped exact/finite replays, uncalibrated for full continuous refinement or physical utility. No novelty claim. Actual substantive duration and model/resource snapshots are file-backed; setup and unrelated checks excluded.

Independent acceptance:24 kernel declarations with only permitted axioms, critic_acceptance.json. Critic independently reran all12 native processes/84316queries with byte-identical outputs; critic_fresh.json. Abstract guard lemmas do not supply compiled-clock error bounds.
