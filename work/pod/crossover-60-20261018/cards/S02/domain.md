# S02 domain review — bounded-latency release refinement

AI-assisted domain role. Inherited root model; exact identifier unavailable. Root owns timing and PM decisions. Original C6/C8/S01 sources and approved statements remain unchanged.

## Exact question and recovered source

Can the first qualifying sampled reading remain linked to the actual switched plant when delivery latency varies and arrivals can tie or reorder?

Read the frozen roster, C6/C8 reports, C8 HandoffPrefix.lean, HandoffAssembly.lean, HandoffWitness.lean, copied DetectorSampling.lean and ConstructiveWitness.lean, plus S01's accepted assembly wrapper. Relevant source paths are under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-18/method-transfer-01/controls/{detector-bridge-06,constructed-handoff-08}`.

The grid is sample(n)=grid(n)=n/2000, h=.5ms. C6 derives a first guard index k≤1058 from its stronger supplied braking execution and original sensor box. C8 additionally proves k≥605, constructs the same physical braking state through grid(k)+h, then joins the causal C7 continuation. Its Assembly contains continuity, source-specific phase-open old ODEs, both one-sided hold ODEs, actual schedule, pending prefix, and unchanged forward ceiling. `First` is by sample index, not earliest network callback. It is unique for a fixed reading stream.

**The frozen cheap-test premise needs correction.** Under the original grid and every latency in[0,h], strict arrival reversal is impossible. For i<j, arrival(i)≤arrival(j). Equality occurs exactly when j=i+1, latency(i)=h, and latency(j)=0. Strict reversal requires a changed assumption, such as earlier latency.75ms with next latency0. That expanded bound also makes the simple held-cell age upper bound1.25ms, beyond the existing1ms contract.

## Adapter and preserved objects

Keep sampling, physical timestamps and payloads unchanged. Define raw arrival(n)=grid(n)+latency(n), and release(n)=max(raw arrival(n),grid(n)+h). With the stated latency upper bound, release(n)=grid(n)+h exactly. Therefore all source clock identities, strict release order and1ms whole-cell ages remain unchanged.

This is de-jitter buffering, not an early arrival-triggered plant switch. It assumes genuine packets, no loss, correct sample identity, and delivery to an actuation-ready queue by the bound. Validation/computation must fit that bound, or the formal event at a deadline must process reception before its scheduled commit. Arbitrary extra processing jitter is not covered. No physical timestamp is renewed when a packet is delivered.

Before and through first index k, the payloads are the source readings m. Later packets are C8 `newReadings` generated from the same constructed actual hold state and admitted sensor errors. Counterfactual future braking readings are never substituted. In particular, a packet sampled exactly at commit can share the continuous physical state, but its sensor error realization need not equal the old source reading.

## Source-bound proof package

`domain_binding.lean` proves `buffered_source_handoff`, which derives k through the original existence theorem and returns all of the following together:

- The original C8 Assembly and its same physical trajectory.
- First k on the actual `newReadings` stream.
- release(k)=grid(k)+h; every earlier packet is available, and earlier releases are strictly earlier.
- Exact full-state equality with the original braking path through release(k).
- Actual sensor boxes against that same trajectory through the finite horizon.
- Every future release clock equals the original translated source clock, and every payload equals the corresponding original hold schedule measurement.

Thus the adapter has a mathematical refinement into the actual source assembly, not merely a generic queue ordering theorem. It does not prove correctness of an unspecified implementation or a physical network driver. It retains the source assumptions supplying the initial braking execution and bounded future cell choices. Source Assembly existence is finite; S01's infinite extension was inspected for binding context but is not silently substituted for this theorem.

## Quantifier boundary for future choices

The theorem is universal over any supplied bounded arrays R,delta,epsilon. It is not restricted to one existentially selected example or one constant input. Once an adaptive policy produces a consistent realized array satisfying those bounds, that realization can instantiate the theorem. However, the theorem does not itself construct arrays whose entries are defined by a state-dependent policy or solve a circular future-dependent specification. Source node_recurrence uses rate/error at n+1, prior sampled node n with epsilon_n, and current physical node n+1. The new `finite_data_prefix` lemma checks that stage n is unchanged when rates and disturbances agree at indices1 through n and measurement noise agrees before n. This is a sufficient nonanticipation statement for the actual source state recursion; it does not construct the choices. S01 already identifies construction of causal history-dependent streams as a deferred continuation task; this review does not claim to close it.

## Discriminating physical-source negative control

The exact C8 witness has First index632, sampled at.316s and committed at.3165s. Set latency632=h and latency633=0: raw arrivals tie at.3165s. Packet632 qualifies. The actual generated packet633 has measured velocity19/1250=.0152m/s, exceeding the guard cap.01122; its source sensor error is+.005 and actual arrival velocity is.0102. Hence it fails the guard.

`domain_tie_witness.lean` proves these facts from HandoffWitness and the actual `newReadings`, while showing the buffered releases remain strictly ordered. A latest-index-only receiver that coalesces this tied batch discards the true first qualifying packet and tests a failing newer one. This falsifies preservation of the first-index/plant-link contract. It is not an unsafe-trajectory proof or a claim about the changed path after that receiver fails. At the tied instant the original pending prefix still supplies the physical state, so the negative control does not require counterfactual future braking readings.

## Queue consequence

A receiver retaining packets only until scheduled release needs at most one resident index between commit instants. Inclusive receive-before-release semantics can temporarily require two consecutive indices at a commit boundary. The exact proof is grid(j)≤t≤release(i)=grid(i)+h, hence j≤i+1; with strict t<release(i), j≤i. These cardinality theorems assume scheduled release is obeyed: queued indices satisfy t≤release(index). A stalled receiver can retain overdue packets and accumulate a larger backlog; that violates the queue theorem premise even when network latency is legal. They also do not include separate storage for arbitrary duplicates or retransmissions, which are outside the declared exactly-one-genuine-packet stream.

## Artifacts, verification and limitations

- domain_clock.lean:7 declarations: no strict reorder, exact tie characterization, release equality/readiness/order, prefix availability and whole-cell age.
- domain_binding.lean:1 source-bound assembly/refinement package.
- domain_tie_witness.lean:4 declarations: bounded witness latency, actual packet633 velocity, guard failure, and tied batch with preserved release order.
- domain_queue.lean:5 declarations: inclusive and strict queue spans, actual finite queue cardinalities≤2 and≤1, and an explicitly expanded-latency reversal/age counterexample.
- domain_nonanticipation.lean:1 declaration: sufficient finite-data prefix agreement for the actual source state recursion.

All18 declarations have producer compilation logs with the permitted axiom set.

The isolated compiler wrapper checks the27 entries in source_sha256 recorded in C8 verification.json and uses its original pinned Lean4.35 environment and existing copied dependency oleans. It compiles only our new files; this is not a fresh rebuild of all58 earlier source modules. Failed parser/elaboration attempts are preserved separately and not counted as accepted proofs. All successful printed closures must contain only propext, Classical.choice and Quot.sound. Independent critic replay passed all five domain modules: exit0, current file hashes match critic_lean_replay.json, and all18 printed closures use only the permitted axioms. The earlier failed clock replay is preserved separately.

Recommendation: **GO** for the known-bound release adapter. Next discriminating test is a concrete receive/validate/commit event-state machine that enforces the two-slot boundary policy and refines exactly to this source-bound package, including the632/633 failing latest-only fixture. Add deadline misses, duplicates and processing-time violations as explicit rejection cases rather than silently extending the latency model. Do not claim strict reordering was fixed within a model that already forbids it.

Quality18/20=90% (A−): faithfulness4, reproducibility4, discriminatory value4, critique3, actionability3. Subjective confidence97% in the mathematical scope after accepted replay; no hardware or runtime implementation acceptance is claimed.
