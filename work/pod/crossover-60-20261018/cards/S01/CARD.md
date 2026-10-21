# S01 — from finite constructed handoff to ongoing execution

AI-written research. **GO: the fixed-stream route produces a source-bound global extension with the same ceiling.** Final timed completion is recorded in `state.json`. The new theorem suite is isolated here; no original C7/C8 file was changed.

## Original question and evidence

Can the finite recovery/detector/pending/hold construction extend consistently to one infinite non-Zeno execution with the same safety ceiling? Frozen sources are the C8 constructed-handoff-08 and C7 constructive-hold-07 reports under the original research notebook. Their hashes and snapshots are recorded in `source_binding.json`. Actual ConstructiveClock, ConstructiveFlow, ConstructiveHold and HandoffAssembly definitions were inspected.

The earlier result constructs each finite path from supplied braking input, fixed half-millisecond clock, and bounded rate, physical target-error and sensor-error streams. Its limitation explicitly excludes inferring infinite execution from a formula outside its proved horizon. The crucial recovered fact is stronger than arbitrary finite existence: the constructor already takes ONE global set of streams R,δ,ε and uses a horizon-independent recursion. Existing one-step state, reading and command lemmas preserve the entire earlier prefix.

## Transfers and what they preserve

1. **Compatible-prefix gluing.** Strengthen one-step preservation to every later finite stage. A covering-stage selector defines one global state; compatibility makes the value independent of which covering stage is selected. This preserves physical state, actual readings and commands, not merely a scalar bound. Arbitrarily long unrelated finite witnesses would not suffice.
2. **Stream recursion and local analysis.** At each time choose a strictly longer finite stage, fixed on a neighborhood. Transfer continuity and both one-sided derivative contracts from that stage. Choosing a horizon exactly equal to the target time would lose the outgoing derivative at a terminal cell. Selector jumps are mathematical representation changes, not physical switches.
3. **Unexpected event-history transfer.** Treat the physical prefix, sensor stream, first guard and clock as one coherent history. A state-only checkpoint can hide incompatible readings and future commands. The detector index is selected once before the horizon, and old readings are retained through AND including that index.
4. **Compactness/branching, tested as a failure route.** A fixed-root tree may have arbitrarily long finite countdown branches and no infinite branch. Positive but shrinking step lengths may be Zeno. The actual source avoids these failures through fixed causal streams and a uniform clock; no compactness theorem or fresh horizon-dependent choice is needed.

## Source-bound proof advance

`domain_prefix.lean` proves nine statements using the actual frozen constructor: later-stage state/reading/command agreement, clock independence, covering-stage existence, one global state, global reading agreement and the original all-time hold ceiling.

`domain_global.lean` proves that the SAME global state satisfies the actual C5 `Execution` predicate on every compact horizon, including continuity and both one-sided ODEs. It uses a strictly larger stage for neighborhood transfer. The actual source schedule theorem supplies local finiteness of dispatches, giving non-Zeno scheduling with the half-millisecond clock.

`domain_handoff.lean` defines one absolute-time global trajectory from the old braking path and global hold. It proves agreement with every sufficiently long finite C8 assembly, matching generated readings, and the unchanged all-time ceiling

    x(t) ≤ 3013722449 / 20100000000,   t≥0.

This is exactly 3/20−1277551/20100000000, not an improved clearance.

`domain_assembly.lean` derives the first qualifying index k ONCE from the original braking/readings assumptions. Its existence wrapper packages every compatible finite assembly, the same first guard for globally generated readings, the full old physical prefix through command arrival, all generated sensor boxes, and the all-time ceiling. No assumed future execution, assumed first guard, or new safety margin was substituted.

The source assumptions remain material: admitted braking input; bounded fixed global streams; rates in [8,12]; physical target error≤.01; sensor component errors≤(.001,.01,.05); and the source guard/prefix contract. The result concerns this scalar, piecewise-constant-response subclass. It does not prove every physical plant supplies those inputs, arbitrary time-varying cell dynamics, maintained rest, a lower travel limit or robot safety acceptance. The old .05-second recovery join remains phase-open; it is not silently strengthened into a classical derivative there.

`domain_absolute.lean` adds five declarations: joined-path continuity, join value, absolute incoming/outgoing ODEs, and `exists_infinite_execution`. The last derives one k and binds it to ongoing Execution, non-Zeno schedule, old/pending prefix and unchanged ceiling. `domain_phases.lean` adds two declarations preserving the original open loss/braking phase intervals. In total, **25 actual-source declarations across six files** independently pass; four generic PM lemmas and three negative-control lemmas bring the supporting total to32.

Both existence packages expose First on the SAME original m. Source `first_unique` identifies their k values; after substitution all physical/readings/stream terms coincide. This does not prove uniqueness across different future streams.

## Independent tests and failure cases

The critic independently replayed the source-bound proof files against the original pinned Lean4.35 environment and checked 27 recorded dependency-source hashes. Root freshly copied and rebuilt the NEW bridge modules in a separate replay directory. Existing dependency oleans were reused: this is not a fresh rebuild of the earlier58-module verification campaign. New proof closures use only propext, Classical.choice and Quot.sound. Root's generic gluing lemmas and three critic structural counterexamples are separate supporting artifacts, not substitutes for actual-source binding.

A source-specific exact counterexample retains C8 k=632, the physical pending prefix, rates and target errors, but changes an admissible future acceleration-reading error between±1/40. Physical states agree through local2h, while next readings differ1/20, commands differ−1/40 and outgoing jerk differs−3/10 at rate12. Therefore finite horizons cannot reselect their sensor stream and still claim one execution. Independent Fraction reconstruction checks the actual center, clipping inactivity and command values.

Other negative controls show: retaining readings only before k can move the first guard632→633; independently varying latency within[0,h] can tie adjacent arrivals; positive h/2ⁿ steps accumulate; and an infinite decreasing natural countdown is impossible despite arbitrary finite branches. These weaken required premises and do not refute the original source.

The inventor's3,930 structural prefix checks and434 selector/clock checks use exact symbolic held-flow terms. They test indexing and history preservation, not analytic ODE existence or all natural indices. Kernel statements supply the unbounded claims. Initial namespace/import/root-directory failures are preserved and excluded from accepted proofs.

## PM decision

**GO** for a bounded causal-environment construction after all60 initial reviews. The original fixed-stream mathematical gap is closed; another wrapper would add little. Next30minutes: choose bounded sensor errors from the current sampled state and available history, then rate/target errors from dispatch history; build streams by well-founded node recursion and prove they instantiate the accepted global trajectory. Predeclare one state-reactive corner policy and a future-dependent no-fixed-point control. Preserve the half-ms clock, phase-open source boundaries and same ceiling. A finite rollout alone cannot pass the all-time causal-existence gate. Semantic binding mutations are recorded in `next_block_protocol.json`. No general plant, novelty or hardware claim.

Quality rubric: faithfulness4, reproducibility4, discriminatory value4, independent critique4, actionability3 = **95/100**. Subjective confidence is high in the scoped formal extension; physical applicability and novelty are unestablished. Root PM plus the three reused workers used the inherited working model, exact runtime ID unavailable. No model-family diversity or Spark inference is claimed.
