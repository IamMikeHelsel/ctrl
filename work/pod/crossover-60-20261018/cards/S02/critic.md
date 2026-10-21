# Independent critique: S02

**GO for a per-index de-jitter adapter under the original complete-delivery/shared-clock contract; NO-GO for latest-timestamp-only detector selection.** Larger delays, dropped messages, timestamp skew, and an implementation-level transport/plant refinement remain separate obligations. Critic model inherited from root; exact ID unavailable. Work is AI-assisted.

## Source binding

Read original C6/C8 reports and actual `DetectorSampling`, `HandoffPrefix`, `HandoffAssembly`, `HandoffReview`, `HandoffWitness`, and relevant `ConstructiveWitness` definitions. Source samples are s_n=n/2000. The bound0≤d_n≤h=.0005 implies arrival(i)≤arrival(j) for i<j: **strict reordering is impossible**. Equality occurs only for adjacent indices with old delayh/new delay0. Any strict-reordering example needs an explicitly larger delay bound or changed clock.

The source `First` predicate requires a qualifying k and every prior index to fail; age/freshness alone does not establish it. C8 preserves physical state through s_k+h, including the entire pending interval, and generates future readings from the constructed state. Retaining old counterfactual braking readings after the switch would violate this binding.

## Independent exact counterexamples

`critic_protocol.py/json` use the source admitted physical witness x=.001+.39t−.6t², v=.39−1.2t, a=−1.2. All0..631 readings fail;632 has v=.0108 and qualifies. A permitted+.01 velocity error at633 gives.0202, which fails. Delays(h,0) tie both arrivals at.3165; latest-index overwrite discards632 despite both ages being valid. This is detector failure, not a proved unsafe physical trajectory.

Further exact controls expose premature commit when both tied packets qualify, strict-before-deadline processing that misses a packet arriving exactly at its deadline, a dropped qualifying packet, and clock skew hiding a true1.1ms age behind a nominal.9ms age. A strict-reorder example explicitly uses changed latency1.5h.

The stronger domain witness uses the **unchanged actual C8 generated packet633**, whose velocity is.0152 from the source+.005 noise, rather than the separate modified-noise diagnostic. It also fails the guard while632 remainsFirst. Both examples must retain their distinct provenance.

## Repair and independent finite audit

Release each genuine indexed payload at s_n+h, never retimestamp it and never replace it with an early n+1 packet. At that release the original common-latency clock, pending interval, held-cell age≤1ms, and C8 physical construction are recoverable. Every due packet and prior prefix must have been ingested before commit. Closing the entire wall-clock tie batch is sufficient but stronger than necessary: the future n+1 packet need not block release n.

`critic_delivery.py/json` independently enumerate the finite event words and reproduce PM's11,520 traces,954 latest-only failures, zero ordered-release failures, and maximum queue occupancy2. These cover all five-message Boolean guard patterns, the declared three delay values, and tie callback orders. Boolean patterns are an abstract stronger detector test, not all physically realizable measurement histories.

Transport assumptions are substantive: complete delivery by the inclusive deadline, authentic identity and original payload, shared clocks, no hidden post-release actuation delay, and retention of the pending plant input until release. Mathematical arrival≤deadline does not prove that a runtime callback has executed before a timer callback.

## Consumer limitations caught

`critic_consumer.json` replays the inventor prefix consumer: complete input passes; missing, duplicate, and latest-only inputs reject. A forged632 payload(0,0,−1) still passes because the checker evaluates only supplied guard predicates, without sensor/source binding. This is a logical supplied-payload prefix checker, not an authenticated physical certificate.

`critic_release_first_probe.json` records an initial consumer defect: it accepted arrival before sample time. Its initial expected-index list also came from the received list, hiding omitted indices. The preserved failed prototype has now been corrected: `critic_release_final.json` independently replays243 passing delay patterns and six rejected mutations for early, late, missing, duplicate, unexpected and deadline-order cases. Expected start/count are now independent trusted inputs. Timestamp=i*h is still synthesized rather than checked against a received payload; actual source receipt binding is outside this prototype. These findings do not indicate bugs in the original Lean source.

`critic_runtime_boundary.json` shows why software execution time matters: a packet arriving exactly at its allowed deadline plus1µs processing gives.501ms pending duration and1.001ms incoming held age. Those exceed the original assumptions, without proving an unsafe trajectory. A useful repair reserves processing/actuation readiness time insideh, with network≤h−reserve and processing≤reserve, followed by the same fixed physical release. Merely reporting a callback timestamp is insufficient.

The queue-cardinality theorem requires every stored index to have arrived and not yet passed its scheduled release. It concerns a Finset of unique identities. A stalled receiver can hold three legally delivered packets, or many duplicate copies, while violating these premises; the theorem does not bound arbitrary backlog or storage.

The proposed due-packet priority can reduce application slots to one only while an external ready set retains the other tied packet. This changes where buffering occurs, not a proved bound of one on total transport storage. No independent replay of that final priority prototype is claimed here.

## Formal review

The final clock lemmas prove order/tie characterization, exact release clock, prefix availability, strict release order and age. The source-bound handoff wrapper derives k via the original finite first-guard theorem and packages the actual C8 Assembly, physical prefix through release, same-state sensor boxes, and future schedule/read linkage. It is not an arbitrary raw-arrival controller and does not prove that the Python receiver refines these functions. The concrete tie proof uses actual C8 generated readings. Independent compile logs and SHA256 values are recorded in `critic_lean_replay.json`; the early failed clock replay is preserved separately. All22 printed declarations across six modules independently compile with exit0 and only propext, Classical.choice and Quot.sound. The domain clock dependency was rebuilt into a critic-owned directory before importing it into later bridges.

The finite nonanticipation statement keeps the same first reading and pending function, and requires equality of rate/error choices1..n and sensor choices below n. It then identifies the actual source recursion at stage n. It does not construct causal policy-dependent infinite arrays, prove arbitrary online receiver causality, or authorize importing future counterfactual plant readings.

## Next test and grade

Prove a receiver-state invariant with a fixed expected sequence, immutable payload binding, exactly-once release, and explicit deadline event ordering; then map emitted commands/readings to the existing Assembly. `critic_next_gate.json` specifies20 semantic mutations for the next30-minute block, including paired infinite streams with identical finite prefixes to check nonanticipation. These are proposed tests, not claimed executions. For a larger latency budget, recheck both the original pending-duration limit and total held age; buffering order alone does not preserve those bounds.

Review quality:4/5 for source fidelity, independent exact controls, finite reproduction and formal-binding audit; runtime refinement and hardware validation remain absent. Confidence is qualitative, not a calibrated percentage. Scoped critic Ruff checks pass; repository-wide checks belong to PM.
