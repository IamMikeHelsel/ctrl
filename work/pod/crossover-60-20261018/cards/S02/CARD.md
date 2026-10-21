# S02 — Detector correctness under variable dispatch latency

**PM gate: GO for a fixed-deadline, source-bound release adapter.** Latest-timestamp-only detection is NO-GO. Runtime refinement and physical deployment remain open. This is AI-written research; root and the three named role workers used the inherited root model, exact runtime model ID unavailable. Different roles are not different model families.

Original question: Can first qualifying sampled readings remain causally linked to the switched plant when dispatch latency varies and messages can tie or reorder?

Provenance: original detector-bridge-06 and constructed-handoff-08 reports, whose absolute paths, frozen hashes and current copies are in source_binding.json/source_snapshot_*.txt. The actual C8 HandoffAssembly, HandoffWitness and detector source definitions were inspected. This was previously investigated source, not a catalogue-only claim. Original source and approved challenges were not modified.

## Framing correction

Sampling interval h=1/2000 seconds and original bounded latency0≤λ_i≤h imply arrival_i≤arrival_j whenever i<j. Strict reordering is impossible under those bounds; only adjacent ties occur, exactly when λ_i=h and λ_(i+1)=0. The roster's proposed strict-reorder cheap test therefore needs correction, while its question stays frozen. Expanded-latency examples are separately labeled and cannot inherit the original startup or age budget.

C8 already constructs a finite switched physical trajectory with the actual first qualifying measurement, unchanged braking/pending prefix through sample_k+h, generated future readings, original controller schedule and exact clearance ceiling3013722449/20100000000. Its sampled guard is not required to persist under later noisy measurements.

## Three transfers and their failure tests

1. **Stream completion frontiers to fixed-deadline control.** Release each immutable packet at sample_i+h. Bounded readiness makes release=max(arrival,sample+h) equal the original clock. Preserve physical pending input and actual source measurements; due receipt precedes commit, while future tied packets may follow. Test latest-only overwrite, endpoint callbacks, loss and added processing time. Naiad is prior context, not a novelty claim; see pm_sources.md.
2. **Proof-carrying complete prefixes.** First detection requires exact prior-index coverage and guard evaluation on the actual recorded payloads. A supplied-payload certificate can pass after replacing a genuine measurement; external acquisition binding is necessary. Test missing, duplicate, relabeled and forged records. A trusted stream map is an assumption, not proof of sensor truth.
3. **Unexpected interval-observer transfer: preserve admission evidence rather than fresh guard truth.** Propagate the selected measurement's state box through the actual pending flow. The old admission and a newer failed guard can coexist. A particular exact trajectory witnesses compatibility; a nonempty interval intersection alone does not prove general physical realizability. General interval transport and immediate variable dispatch remain unproved.

## Discriminating evidence

- The unchanged C8 actual stream has First at632. At633 its generated measured velocity is19/1250=.0152, exceeding the guard bound. Delays(h,0) tie arrivals. Latest-only overwrite discards the genuine first qualifying packet, even though both packets are fresh. This is a first-index preservation failure, not a proof of unsafe motion. A separately labeled permitted+.01-noise fixture gives.0202; do not conflate it with the original witness.
- Root and critic independently enumerate11,520 five-packet event traces:954 latest-only failures, zero ordered-release failures, maximum queue2. Boolean guard patterns are abstract protocol fixtures, not all physically realizable histories.
- The repaired inventor consumer passes243 exact delay patterns and rejects six semantic mutations. Critique exposed two real initial defects: negative latency was accepted and a received-list-derived universe hid missing packets. Failed version retained. Payload authentication and Python-to-Lean refinement remain absent.
- Source-bound Lean bridge returns the original Assembly and First on actual newReadings, identical physical prefix and schedule linkage, for every supplied bounded parameter array and finite N≥2. It does not construct an endogenous history-reactive environment. Future counterfactual braking readings cannot replace actual generated readings.
- Kernel queue bounds are≤2 at an inclusive deadline and≤1 strictly between serviced deadlines, with unique indices and no expired queued deadline. A stalled runtime may accumulate3 packets without violating network bounds. A one-slot application implementation merely moves a future tied packet into an external ready queue. Root independently enumerated all six tied receive/commit orderings: three satisfy due-before-commit; one needs one application slot and two need two.
- Network latency h plus any positive unbudgeted processing/actuation delay misses the original clock. Even1microsecond produces.501ms startup and1.001ms incoming held age. Reserve processingρ within h: network≤h−ρ and processing≤ρ imply the original release clock. This is a conditional budget proof, not a measured real-time implementation.

Additional hand-derived distinction, independently challenged by critic: adjacent arrival gap is at least h minus latency dispersion. Reserving positive network slackρ gives raw gap≥ρ, but variable processing can restore a tie in end-to-end readiness. A large common latency offset preserves order while violating the physical age budget; exact diagnostic fixtures are in pm_dispersion.json. This general dispersion statement is not a new kernel proof.

## Independent critique and acceptance limits

Root and critic freshly compile clock7, actual-source handoff1, concrete tie4, queue5 and processing4 and finite-data nonanticipation1:22 printed declarations, only propext/Classical.choice/Quot.sound. Original pinned dependency artifacts are reused after source hash checks; no full closure rebuild is claimed. Logs, exact hashes and declaration lists are in pm_kernel_acceptance.json and critic_lean_replay.json.

Reliable complete delivery, genuine original payloads, shared clocks, bounded validation/actuation readiness, due-receive-before-release ordering and unchanged pending command are substantive premises. Rejection means the original contract cannot be established; no safe fallback for loss or lateness was proved. Finite offline event sorting is not an online causal implementation. No hardware execution, physical safety acceptance, new controller discovery or exhaustive novelty assessment.

Quality rubric: faithfulness4, reproducibility4, discriminatory value4, independent critique4, actionability3 =19/20 (95%). Subjective confidence: high in the scoped exact counterexample and conditional clock mapping; operational applicability remains unverified. The grade is not a success probability.

## Precise next action

After all60 initial reviews, one30-minute block implementing an isolated online receiver invariant and binding its emitted immutable payloads, first decision and actuator times to the actual C8 Assembly. Use the20 predeclared semantic mutations in next_block_protocol.json with unmutated positive partners. Prioritize processing reservation and deadline ordering. A larger-latency route requires a separately proved age/startup contract. Do not extend before breadth completion.
