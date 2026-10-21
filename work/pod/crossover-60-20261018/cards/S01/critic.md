# S01 independent critique

AI-written independent critic; inherited root model, exact identifier unavailable. Original source/challenges preserved. Kernel evidence, exact arithmetic, symbolic dependency checks and physical validation are distinguished.

## Source binding and central finding

Read both frozen C7/C8 reports and actual ConstructiveClock, ConstructiveFlow, ConstructiveHold, HandoffPrefix and HandoffAssembly sources, with relevant detector, schedule and weighted-policy definitions. The finite source construction uses fixed global rate, target-error and sensor-error streams R,δ,ε. Its recursion already supplies state_step_before, readings_step and command_step; this is stronger than unrelated existence of a solution at every finite horizon.

The source clock has no N-clamping: right index is floor(2000(t−h)); left index is ceil(2000(t−h))−1, with natural saturation at zero and h=1/2000 s. At terminal time Nh, right and left indices are N−1 and N−2. A finite state formula extends its final phase beyond its proved interval, but that extrapolation is not its future execution. The finite theorem supplies incoming derivative at its endpoint; the outgoing derivative must come from a longer compatible prefix. Source actual_schedule already proves local finiteness of the half-ms dispatch clock.

C8 retains old readings through and including k, then generates future readings from the constructed physical state and ε. Equality only for j<k is insufficient for the first guard. The initial sample is m, not g(0)+ε0: ε0 is unused. The pending physical path is retained through command arrival σ+h, and rate/error translations are σ+s−.05. The original .05 recovery join remains phase-open; a global continuation must not strengthen it silently into a classical derivative claim. Common latency preserves strict arrival order; independently varying delays in [0,h] can tie adjacent arrivals.

## Independent checks and negative controls

critic_negative.py uses exact Fraction arithmetic for terminal indices, clock relations, guard changes, sensor/command changes and 100 positive shrinking-step checks. A synthetic countdown tree shares a root and has arbitrarily long finite branches but no infinite branch; this isolates the invalid inference from separate finite witnesses. Positive intervals h/2^n accumulate below h, so strict positivity alone is not non-Zeno. These deliberately weakened-premise counterexamples do not refute C7/C8.

critic_structural.lean independently compiles three standalone theorems: no infinite strictly decreasing sequence of naturals, an exact differing-sensor-command witness and the variable-latency tie. Its axioms are within the permitted set. The synthetic command witness is a local subsystem example, not a claim of a full C8 execution.

critic_readings.py independently checks the inventor's stronger actual-source sensor fork. It reconstructs the k=632 braking state and pending endpoint, the source weighted-policy center, sensor boxes and both unsaturated commands using exact rational arithmetic without producer imports. Two ε1 acceleration values ±1/40 share the physical path through local 2h but produce commands 1335629/6250000 and 1491879/6250000; the difference −1/40 yields outgoing acceleration-derivative difference −3/10 at rate12. Thus agreement of physical states alone does not identify histories with changed sensor streams. Fixed-stream prefix gluing survives this control.

The inventor's structural term comparison treats heldSolution as an uninterpreted exact-flow symbol. Its unequal out-of-horizon expressions demonstrate changed dependencies, not by themselves numerical inequality of physical states. The exact sensor-fork calculation supplies an actual differing derivative under the source assumptions.

## Promoted source bridge

The final domain_prefix.lean independently compiles nine declarations against the original pinned toolchain. All use only propext, Classical.choice and Quot.sound. Its hash is 63b5da5a3a5e1b5aeff9014e5f1e15bd75a3557010a66dde3c13facb2c61ba84. The audit checked 27 source_sha256 entries in the original verification report; it used existing compiled dependencies and is not a fresh rebuild of the entire prior source closure. My earlier message saying58 confused reported build count with this source-hash count; corrected explicitly.

The bridge proves actual recurrence-prefix equality, reading and command equality, clock independence, a single globalState chosen from covering stages, and the unchanged safety ceiling for all nonnegative times. The stage choice changes no controls or histories. The initial attempted replay failed on ambiguous measure names and produced sorryAx diagnostics; that log is retained, the names were qualified, and only the corrected successful version is promoted.

A same-path all-time ceiling is stronger than pointwise unrelated witnesses but still distinct from proving that path is a global Execution. Full continuity and one-sided ODE transfer require neighborhood equality, using a strictly larger finite horizon. C8's global detector/readings/join obligations also remain separate until proved and independently replayed.

## Gate

GO for the direct causal-prefix construction under exactly the original fixed bounded streams and supplied C6/C7 input. No compactness theorem or new physical existence assumption is needed for this route. Acceptance requires one common path, same generated readings and command clock, global one-sided execution, unchanged ceiling, non-Zeno dispatches and C8 prefix/first-index binding. No lower travel bound, maintained rest, arbitrary time-varying within-cell rate, or hardware claim follows.

Subjective confidence in the route is high, not a calibrated probability. Provisional quality 18/20: source binding4, independent checks4, negative controls4, claim calibration4, closure2; update closure only after final global-interface proof replay.

## Final independent replays

The subsequent actual-source files independently compile successfully, with only permitted axioms:

- domain_global.lean: two theorems, including one globalState satisfying the original local Execution on every compact horizon. The proof uses coveringStage(H+1), transfers readings at t and transfers derivatives using eventual neighborhood equality. It preserves one-sided joins. The schedule theorem inherits actual_schedule's local finiteness. SHA-256 ab4b4aa5af25d090af383219bd579cc725534f9b899f6cb38813c70f361f4cc0.
- domain_handoff.lean: four theorems binding the global hold, full trajectory and generated readings to every covered source prefix, plus the unchanged all-time C8 ceiling for a fixed first index. SHA-256 e059f23f1f909949b97af1161879bda5bec760b88c906f1cb12377beb955cc6e.
- domain_assembly.lean: three theorems, including preserved full old/pending prefix, all generated sensor boxes, and exists_coherent_global_handoff. The last derives k once via finite_first_guard before any horizon/time choice; it does not assume a new First witness. SHA-256 a292066fa85a4181bbb35f85d1464db3191cbf4a81ff947bf5ea18cd506f4c14.
- pm_gluing.lean: four generic compatibility, safety and local-continuity lemmas, separate from the actual-source bindings.

These are a source-bound theorem suite. At this stage the existential assembly wrapper itself packages finite Assemblies and global predicates; the global Execution/schedule statements are separate theorems instantiated with the source pending_execution. Do not describe the wrapper alone as a single theorem containing every InfiniteAssembly field.

The fixed infinite input streams are already part of the finite source assumptions, so the construction introduces no requirement to know future readings in advance. Its causal prefix theorem is the relevant mathematical property; the noncomputable stage selector is not a deployed controller implementation. No fresh full rebuild of the original dependency closure or hardware validation was performed by this critic.

Final scoped critic Python Ruff/format checks pass. Structural negative controls and actual-source sensor-fork arithmetic pass. Subjective rubric upgraded to19/20 (closure3/4) for the accepted source-bound global theorem suite, with explicit execution packaging and physical refinement kept separate.

## Final execution packaging accepted

The last two frozen files independently compile successfully, closing the previously noted packaging gap. domain_absolute.lean proves full absolute-path continuity on every compact horizon, the join value, absolute incoming/outgoing ODEs after the decision, and exists_infinite_execution. The existential wrapper derives one k from the original detector theorem and explicitly binds that k to the same global hold Execution for every nonnegative horizon, the same schedule/local finiteness, the continuous joined path, preserved old/pending prefix and unchanged all-time ceiling. Its SHA-256 is ec8a399d2c05e5cdae9e5987c34f2c18dbb4a86d7b730e76638d52c19cc3e561.

domain_phases.lean preserves exactly the old phase-open loss and braking ODE intervals, including the pending segment and excluding any new derivative claim at .05. Its SHA-256 is e4c5447e7db6feb1d5149c9b0f82358576ebbcbe89bda4baf7edd3679737f31c. All seven last declarations use only permitted axioms. The global sensor-box/first-reading proofs from domain_assembly concern this same source-defined path and first index; source first_unique prevents incompatible choices across wrappers.

Final accepted actual-source count:25 declarations across six files, plus four generic PM lemmas and three critic negative-control lemmas. This closes the mathematical finite-to-infinite execution gap for the stated scalar piecewise-constant digital-rate subclass and fixed bounded streams, conditional on the original supplied braking input. It does not extend that input class, improve the ceiling or prove hardware behavior. Final quality remains19/20; no open mathematical packaging gap is retained in this review.
