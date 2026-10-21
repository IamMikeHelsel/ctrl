# S01 cross-discipline inventor

AI-written research; inherited root model, exact model identifier unavailable. Root owns the timer and PM decision. This role changed only S01 inventor artifacts. Original C7/C8 sources, toolchains and approved statements remain unchanged.

## Frozen question and source recovery

Extend the actual finite recovery/detector/pending/hold construction to one infinite non-Zeno execution, retaining the same ceiling and the full states, readings, clock and one-sided ODE contract. A scalar ceiling alone is not an execution.

Read both report snapshots and the actual source files under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-18/method-transfer-01/controls/`:

- `constructive-hold-07/build/ConstructiveClock.lean`, `ConstructiveFlow.lean`, `ConstructiveHold.lean`, `ConstructiveWitness.lean`, plus the command, policy and index definitions in `DigitalHold.lean`, `ClearancePolicy.lean`, `WeightedEntry.lean`, `DelayedWitness.lean`.
- `constructed-handoff-08/build/HandoffPrefix.lean`, `HandoffAssembly.lean`, and `CLAIMS.txt`.

The source already has more structure than “arbitrarily long finite runs exist.” It accepts fixed global streams R,δ:Nat→Real and ε:Nat→State with bounds for every index. `state n` is one horizon-independent natural recursion. Its finite Execution theorem is proved through grid(n+1), with h=1/2000. The existing `state_step_before`, `measure_step`, `readings_step` and `command_step` are exactly the compatibility ingredients. C8's first index depends on the retained original reading prefix; its hold is the same C7 constructor shifted by sigma=grid(k). No new detector decision or pending initial state should be chosen at each horizon.

## Transfer 1: compatible-prefix gluing, without a compactness claim

Map each finite constructed state/readings pair to its restriction on its proved interval. `state_step_before` says the next state restricts to the old state through grid(n+1); the corresponding reading and command lemmas retain the observations and input fields. Inductively, state m agrees with state n through grid(n+1) whenever n≤m. This is an eventual-value construction, not convergence of numerical trajectories.

A concrete global selector is

    F(t) = state(ceil(2000*max(t,0))) t.

For t≥0 its chosen finite theorem covers at least one cell beyond t. For any fixed M, F agrees with state M on [0,grid M]. To prove continuity or an ODE at t, choose a **single** M with grid M>t and transfer the finite theorem on a neighborhood. Do not differentiate the ceiling selector, and do not treat the selector's jumps as additional physical events. At t=0 use the source right-sided startup obligation; at dispatches transfer the distinct incoming and outgoing fields.

The actual obstruction is precise: choosing a theorem whose final horizon equals t does not supply the outgoing ODE, because `right_ode` excludes the final endpoint. A strict larger horizon resolves this. The old recovery boundary at .05 retains its original phase-open contract; nothing here creates a classical acceleration derivative there.

Preserved objects: all three coordinates, initial/pending prefix, sensor boxes, causal command, index/stamp fields and one-sided derivatives. Required assumptions: the same admitted streams and initial data across n, prefix equalities, and unbounded positive clock. Falsifiers: mismatched sensor streams, lack of strict local coverage, or conflating incoming/outgoing indices. A proof only of pointwise safety would fail this transfer.

## Transfer 2: causal stream recursion with the needed memory

The endpoint recurrence is a second-order transducer: node(n+2) depends on physical node(n+1) for the exact held-flow initial condition and on node(n) plus ε(n) for the delayed sample. Its state must therefore include the adjacent physical nodes (or equivalent queued-reading memory), not just current x,v,a. The first sample is authoritative m; ε(0) is unused. Rate and physical target-error choices for the new cell are R(n+1),δ(n+1). This recursion gives a unique generated prefix for a fixed input stream without solving a future implicit execution equation.

The clock itself already excludes Zeno: dispatch(n)=(n+1)/2000, so a bounded nonnegative time T contains floor(2000T) dispatches. The exact translation sigma+grid(j)=grid(k+j) keeps C8 on the original clock. A fresh local clock without that equality would change sample age and the theorem assumptions.

Preserved objects: delayed causal information, physical node identity, whole pending prefix and absolute sample/arrival timestamps. Breaking conditions: current-reading substitution for the previous sample, renewing a queued timestamp, losing the older node, or admitting an online coefficient rule without proving its bounded causal stream contract. A positive fixed h is sufficient; arbitrary finite executions with shrinking step lengths are not.

## Transfer 3, unexpected: immutable event histories rather than independently chosen runs

An event-sourced system must retain the same accepted observations and queued inputs when extending its history. The mathematical analogue is that the object being glued is an execution record, not just a geometric state curve. This gives a sharp failure test using the **actual C8 polynomial witness**, not an unrelated toy dynamics.

Fix k=632, sigma=.316, the source braking state, the first reading m, all rates and target errors. At local sample 1 choose acceleration sensor noise +1/40 for one finite construction and −1/40 for another; both lie in the source ±1/20 box. Their physical states agree through local 2h: the pending prefix and first held cell use the same m and other inputs. But the readings at local h differ by 1/20. The commands arriving at 2h differ by −1/40, both strictly inside the clip interval. With the common R(2)=12, the outgoing acceleration derivatives differ by −3/10.

`inventor_stream_counterexample.py` computes the policy radius/center from the actual source formula and checks all these rational equalities. It reproduces the first digital command .22264264. The later commands are 1335629/6250000 and 1491879/6250000. Their common physical state at the second dispatch need not be numerically approximated: it cancels from the derivative difference. Equality of that prefix follows structurally from the source recurrence; this role has not newly kernel-checked the entire execution closure.

This does not refute a fixed-stream infinite construction. It refutes gluing arbitrary independently selected finite witnesses merely because their physical prefixes or safety ceilings agree. The actual source's horizon-independent streams avoid the problem. The analogy adds no hardware reliability claim, distributed consensus assumption, or external messaging.

## Transfer 4: test the tempting compactness shortcut

“Every depth has a finite path” alone need not supply one infinite path. As an elementary abstract counterexample, a rooted tree can first select any natural n and then require strict descent n,n−1,...,0. It has arbitrarily deep finite branches but no infinite branch; its root has infinitely many choices. This is not a C7 plant counterexample. It identifies the missing hypothesis in a bare existence argument and explains why the explicit compatible source recurrence is stronger and preferable here. Real-valued cell choices must not silently be treated as a finite-branching tree.

Likewise clocks t_n=1−2^(−n) have arbitrarily many finite events but accumulate before time 1. The source's fixed h and translated clock rule this out directly. Neither abstraction should be imported as a claim that the source has such a failure.

## Exact checks and limitations

`inventor_prefix.py` performs 3,930 exact full-state/reading/side checks for finite horizons N=2..11 and extensions through 14, at grid boundaries and quarter-cell rational probes. It preserves the full three-coordinate state as a source-shaped symbolic held-flow term, and verifies reading indices, timestamps and ages: incoming age 1/1000 and outgoing age 1/2000 at dispatch. It tests translated clocks at k=0,632,1058 and the finite dispatch count. It deliberately checks that equal final state does not make the old totalized finite formula a justified outgoing extension beyond its theorem horizon.

An additional 434 exact selector checks verify F(t)=state M(t) on the sampled common intervals and confirm that the selected finite horizon extends at least h beyond t. Distinct extrapolation terms are reported only as a structural negative control; syntactic inequality alone is not proof that two arbitrary symbolic flow expressions denote different physical states.

These are **structural term and exact clock tests**, not exact evaluation of exponential physical flows, a proof of all natural indices, a safety proof, or an ODE existence proof. Their value is to catch shifted indices, lost readings and accidental formula extrapolation before formal integration. The full-state prefix proof should be discharged against the existing source lemma, not inferred from these finite tests.

The rational sensor counterexample separately checks actual source policy/command arithmetic, bounds and unsaturated command differences. It preserves the source execution inputs and makes the need to fix the observation stream concrete. No new hardware or general variable-rate plant existence claim follows.

## Proposed gate

**GO** for the narrow fixed-stream extension: prove the iterated C7 prefix lemma, define one global selector, prove local equality on every bounded interval with a strictly larger finite witness, then transfer full Execution/readings/schedule facts and the unchanged ceiling. Apply the C8 join once at its already established k, preserving braking through sigma+h and translating both one-sided tail fields. The final theorem should state a single global trajectory and single generated reading stream whose every finite restriction has the required contract.

**HOLD** acceptance until that theorem is bound to actual C7/C8 definitions and its permitted axioms are audited. **NO-GO** for fresh witness selection per horizon, scalar-ceiling-only gluing, outgoing ODE extrapolation from a final endpoint, or claiming arbitrary time-varying rates/plant existence. The supplied initial C6 braking trajectory remains a premise.

Quality: faithfulness 4/4, reproducibility 4/4, discriminatory value 4/4, critique 3/4, actionability 4/4 = 19/20 (95%) for this bounded inventor analysis. Subjective confidence is high that the identified source interfaces support this construction; completion and correctness of the full global theorem remain separate until kernel checking and statement review.
