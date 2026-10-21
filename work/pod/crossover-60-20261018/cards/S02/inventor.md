# S02 cross-discipline inventor

AI-written initial review; inherited root model, exact identifier unavailable. Original C6/C8 sources remain unchanged. All experiments use exact rational arithmetic. This role supplies finite protocol and physical-prefix checks, not a new kernel theorem or a constructed variable-latency plant execution.

## Original contract and the distinction that matters

Read `detector-bridge-06/REPORT.txt`, `constructed-handoff-08/REPORT.txt`, `HandoffPrefix.lean`, `HandoffWitness.lean`, and the copied `ClearancePolicy.lean` and `DetectorWitness.lean` under the frozen method-transfer-01/controls source directory in CARD.md. C8 defines First(m,k) as a qualifying reading at indexk and no qualifying reading at any smaller index. Its prefix-stability theorem binds that result to unchanged payloads throughk; its physical prefix remains the braking trajectory through actual command arrival.

With sample spacingh=.5ms and individual dispatch delaysD_i∈[0,h], arrivals cannot strictly reorder: forj>i,

arrival(j)−arrival(i)≥(j−i−1)h≥0.

Ties are possible only between adjacent samples, when the older delay ish and the newer delay is0. Thus the frozen roster's suggestion of constructing strict reordering under these exact bounds is too strong; ties are the relevant original-contract counterexample. A2h delay example is separately labeled and is not quietly substituted for the original problem.

## Three transfers

**1. Distributed stream watermarks and de-jitter release.** Treat physical arrival as readiness to enter a queue. Release packeti at its original timestampih plus the known boundh. Reliable bounded arrival ensures it is available; this restores exactly the common-h schedule used by C8, independent of variable earlier arrival times. Retain the old physical pending command until release. A future packet arriving at the same instant must remain separately queued, not overwrite the packet due for release.

Preserved invariants: immutable sample identity/payload, sample-to-release ageh, held-cell incoming endpoint age2h=1ms, and the original pending/handoff boundary. Required assumptions are explicit: all expected payloads become validated and actuation-ready within their deadline budget, the clocks are the original common clock, the due packet is ingested before its release, and no additional processing/actuation delay is hidden outside the bound. The first consumer uses the stronger convention of ingesting every same-time arrival before release; the later priority test shows that future packets may instead follow release. This is an ideal timed adapter proposal, not a hardware scheduler guarantee.

Falsifiers: release before ingesting a boundary arrival, a missing or late packet, latest-cache overwrite, clock relabeling, or queue release that secretly adds more than the existingh delay. Under a larger2h latency bound, release atstamp+2h can restore order but gives3h=1.5ms at the next held-cell endpoint and2h startup delay; the existing C8 age/startup contract no longer follows.

**2. Proof-carrying causal prefixes.** A detector decision is a claim about a complete prefix, not a property of the newest value. Attach a certificate that the actual payload at indexk qualifies and every actual earlier payload fails. A finite monitor can retain a contiguous-processed frontier and the earliest qualifying index. A newer nonqualifying sample is not evidence that an earlier unprocessed sample failed.

Preserved invariant: the source First predicate on the actual reading stream. The small checker requires exactly one record for every index0…k and rejects missing/duplicate indices. It then checks guard truth. This logical predicate alone is still insufficient: changing the selected payload to another qualifying measurement preserves First on the supplied records. A second checker compares every record against an externally trusted immutable actual-stream map. That map must come from the acquisition/history interface, not from the certificate itself.

Falsifiers: a gap falsely labeled a complete prefix, duplicate identity with conflicting data, a certificate produced for another valid-but-unobserved payload, or later measurements from counterfactual continued braking after a switch. C8's existing prefix stability is directly relevant, but an acquisition-to-actuator consumer still needs to bind the theorem arguments. Immediate release upon certification could use less latency, but reusing C8's fixed-h construction then requires a separate variable-dispatch pasting proof; the watermark route avoids that extra change.

**3. Unexpected transfer from interval observers: transport evidence instead of demanding guard persistence.** A qualifying measurement is an admission fact at its timestamp. Carry its bounded-state evidence through the actual pending ODE to the arrival time. A later noisy measurement may fail the detector guard while remaining physically compatible with that old admission. This is a different issue from message ordering: a guard on noisy readings is not a monotone state property.

The exact witness uses the known pending target−1.2, which lies within the old acceleration interval[−1.25,−1.15]. Positive response rates preserve that acceleration interval. Integrating its endpoints and the old velocity interval gives a conservative arrival box, which can be intersected with the new measurement's box. The actual polynomial trajectory supplies an explicit joint witness; mere nonempty interval intersection is not treated as proof of physical realizability. This transport preserves the original admission history rather than recentering the controller or inventing a newer qualifying measurement.

Falsifiers: assuming guard persistence under arbitrary bounded noise, treating a box hull as an exact reachable set, changing the pending target without rebuilding the transport, or replacing the selected reading and center with a fresh measurement while claiming the original handoff theorem. General interval transport for all C6 braking inputs remains a separate proof task.

## Exact source-grounded counterexample

`inventor_latency.py` reconstructs the source polynomial prefix

x=.001+.39t−.6t², v=.39−1.2t, a=−1.2.

The actual C5 guard uses position≤.143, |measured velocity|≤561/50000=.01122, and acceleration in[−1.27,−.2]. All readings through632 are exact. At633, choose a new permitted velocity sensor error+.01, with zero position/acceleration error. This is a valid new noise fixture on the source physical prefix, not a claim that the original C8 witness used this exact future noise vector.

| quantity | sample632 | sample633 |
|---|---:|---:|
| timestamp |79/250|633/2000|
| actual position |10051/156250|1286633/20000000|
| actual velocity |27/2500|51/5000|
| actual acceleration |−6/5|−6/5|
| measured velocity |27/2500|101/5000|
| guard |true|false|

Every earlier exact reading fails the speed guard, so632 is first. Delays(h,0) make both packets available at633/2000=.3165. Their information ages areh and0. A latest-timestamp-only consumer that handles633 first then discards632 records no qualifying packet in this two-message prefix. Reversing callbacks records632. This refutes first-index preservation and callback-order independence; it does not prove that the controller will never detect a later guard or that an unsafe physical trajectory results.

De-jitter release times are.3165 for632 and.317 for633. The second packet cannot displace the first at the earlier release. The old and new readings are physically compatible: the transported old velocity interval is[7/40000,809/40000], the fresh interval is[51/5000,151/5000], and the actual arrival velocity51/5000 belongs to their intersection. The script checks position and acceleration as well. A fresh failed guard therefore does not invalidate the particular older admission and pending trajectory.

## Executable consumer and negative controls

`inventor_release.py` checks243 exact five-packet delay patterns with each delay chosen from{0,h/2,h}. Tied arrivals are deliberately ingested newest first; every packet still releases in source index order atstamp+h. At most two packets are buffered in these tests. The general memory bound follows from every buffered sample stamp lying in[t−h,t] just before release, an interval containing at most two grid points; this argument has not been kernel checked here.

Independent critique found two implementation gaps in the initial timing consumer: it checked the latency upper bound but accepted a pre-sample arrival, and it derived the expected packet universe from the received-index list. The initial script and result are preserved as `inventor_release_unbound.py.txt` and `.json`. The corrected consumer requires an external trusted expected start/count, constructs deadlines from that interval, and checks arrival≥original sample stamp. The expected schedule must not itself be certificate-controlled. This correction does not add payload authentication.

Six actual consumer mutations now reject: release before boundary ingestion, exceeding the latency bound, pre-sample arrival, hiding a missing expected index by shrinking the received list, duplicate identity and an identity outside the trusted acquisition interval. Rejection means the contract cannot be established; no fallback safety policy is supplied. A separate2h-delay test demonstrates genuine raw-arrival reordering, restored release order, and the resulting failure to preserve the original1ms age and.5ms startup limits.

The prefix checker rejects a missing index, duplicate index, and newest-record-only pseudo-prefix. The unbound logical checker accepts a selected position shifted by.0001 while its guard remains true; the externally bound checker rejects that changed payload. Both behaviors remain executable and recorded. The release consumer itself models identity/stamp ordering only; it does not independently authenticate sensor payloads or instantiate the full plant theorem.

## Logical event order and storage are separate contracts

`inventor_tie_priority.py` weakens the boundary ordering requirement: ingest the due packet, release it, then ingest a future packet whose arrival has the same real timestamp. All243 five-packet delay patterns pass with one application payload slot under this deadline-priority interface. The external ready list can still contain two packets. This is not a proof of one total physical storage slot.

The exact tie at.3165 has logical events ingest632, release632, ingest633; release633 occurs at.317. With arbitrary immediate FIFO callbacks, the reverse order633 then632 cannot be accepted losslessly by a single application slot: the future payload occupies it when the due payload arrives. Deferring that future callback requires storage or scheduling support elsewhere. The experiment preserves both outcomes instead of treating a hidden ready queue as free memory.

All events sharing a real timestamp are ordered logically in this model. No processor is asserted to execute validation, scheduling and actuation in zero time. A10-microsecond service cost added after the nominal deadline would make initial dispatch age.51ms and the next incoming held-cell age1.01ms, exceeding both original bounds. If that service is reserved, readiness would need to occur by.49ms within the same total. The actual latency assumption must cover validation and actuation readiness, and any positive final service cost must remain inside the original stamp+h deadline. A raw network-arrival guarantee alone is insufficient.

## Decision

GO for a source-bound stamp+h release adapter under explicit reliable bounded readiness, immutable payload and boundary-order assumptions. This is the cleanest route to reusing C8's existing clock and physical handoff construction. Next: connect the queue's released packet to the exact schedule measurement at every index, including the first selected reading and later generated readings, and prove that tied arrivals cannot replace a committed prefix.

GO for a small complete-prefix certificate consumer with external acquisition binding; keep its guarantees separate from packet age. HOLD the general interval-observer transport and immediate variable dispatch until their physical proof bridges are supplied. NO-GO for latest-timestamp-only first detection, for silently calling ties strict reordering underD≤h, or for reusing C8 after changing the delay bound to2h without a new age/startup proof.

Evidence: exact rational fixture and finite consumer tests, plus explicit analytic bounds and inspected source definitions. No new inventor Lean theorem, general queue/plant existence result or hardware validation. All three current scripts pass Ruff. Quality: faithfulness4/4, reproducibility4/4, discriminatory value4/4, critique4/4, actionability3/4 =19/20 (95%). Subjective confidence is high in the tied-arrival counterexample and exact clock mapping; operational reliability and source-bound hybrid integration remain unverified.
