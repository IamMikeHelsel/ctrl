# R01 — cross-discipline inventor

AI-written; inherited root model, exact identifier unavailable. Root owns session timing and PM decision. No robot commands, source changes, gain changes, or alteration of the0.2mm tolerance/tracking radius.

## Question, provenance, and prior result

What authoritative task information distinguishes a true small move from noisy observations of a hold without silently suppressing intended motion? Inspected frozen sources:

- `research-notebook/research/pods/2026-10-17/robot-motion/intent-contract-07/analyst/report.md`
- the same directory's `motor-control-addendum.md`
- `research-notebook/research/pods/2026-10-17/robot-motion/task-contract-08/builder/report.txt`

All paths are under `/Users/mike/Dev/ctrl-research-notebook/`. Prior work already gives identical-history impossibility and an isolated authoritative-goal theorem with target, epoch, deadline, bounded delivery/admission, completed old tail, and persistent physical state. It proves position progress/arrival, not full physical rest. This session examines information precision and protocol composition gaps rather than rediscovering that impossibility.

## Four transfers with explicit falsifiers

1. **Semantic confusability and finite coding.** A message class may merge task truths only when one output satisfies every surviving truth. Preserve the original goal bands and the controller's shared observable history. Break: an abstract bit count depends on the predeclared goal alphabet, available side information, and whether the requirement is position or actual movement. Falsifier: with identical observed packet1mm, true goals0,.5,1mm and0.2mm position bands are pairwise incompatible. A truthful hold/revise bit aliases the two moves. Exact enumeration finds no valid two-symbol encoding and six valid three-symbol encodings. Thus this finite example needs at least three semantic symbols, or two fixed noiseless bits—not a universal minimum command length. Conversely, goals0 and.1mm have overlapping position bands, so one fixed position can satisfy both; that does not prove the intended movement occurred.

2. **Distributed command processing and transaction identity.** Treat a revision's identity and payload as a record whose effect is appended at most once to the reference history. Preserve the original authoritative target/deadline and the completed-tail rule. Break: idempotency at the high-level absolute-goal receiver does not automatically survive a downstream transport of compiled displacement events. Falsifier: replay the compiled1mm displacement after compilation; both copies can satisfy the jerk limit while producing a2mm reference for a1mm task. This is a hypothetical interface failure, not a discovered bug in an existing pipeline.

3. **Predictive command copies, carefully separated from intent.** A ledger of admitted execution times and applied commands can feed a state predictor; a requested goal alone is not such a ledger. Preserve the distinction between desired task, committed reference, and measured/estimated state. Break: a predictor using nominal issue time can predict movement before admission or execution, and an accurate predictor still cannot reveal unissued or falsely labeled intent. Falsifier: copy the original20mm request with nominal execution.22s while the actual event is delayed to1.3s. At1.02s, nominal-reference prediction is20mm but the actual committed reference is0. This violates the original delivery premise, rather than refuting its theorem.

4. **Unexpected: proof-abstraction precision as a communication budget.** Interpret target encoding error as another uncertainty set to be composed with the tracking tube. Preserve the original physical toleranceε and certified tracking radiusR. Break: assuming that every error in the tube is physically attainable would overstate this result; it concerns what follows from the interval abstraction alone. Falsifier: ε=R=.2mm leaves no reference margin. An encoded reference1mm, true goal1.001mm, and tube-permitted position.8mm produce.201mm goal error. A finite quantizer cannot claim the existing exact-goal theorem unchanged merely because its rounding error is small.

## Exact information and target-precision experiment

`inventor_information.py/json` uses rational millimeter units. It enumerates all binary encodings for the three original-style competing task truths above. The extra noise-bound1mm example is declared explicitly and leaves the shared observed packet unchanged.

For any R≥0, the requirement

∀e∈[−R,R], |q+e−g|≤R

forces q=g: e=R gives q≤g and e=−R gives q≥g. Conversely q=g suffices. Therefore, for a fixed shared advisory history, each message cell must identify one exact goal if the guarantee relies only on the full-radius tube and ε=R. A finite message alphabet cannot provide this property for every continuous real goal. This does not prove that a particular physical controller cannot do better: a tighter tracking result, task-defined discrete targets, or other authoritative side information would change the assumptions. No such change is silently made here.

The tiny-goal negative control is essential. Overlap of actual-position success bands may allow an always-hold result to satisfy arrival while failing to establish movement. Positive progress needs a separate lower-bound obligation; the original source itself requires |δ|F>R for that tube-based conclusion. Neither a direction bit nor a truthful move label supplies such physical progress by itself.

An optional, separately labeled command-corruption extension checks bounded bit errors. Three semantic labels require at least five fixed bits to correct any one flipped bit; the exhaustive search finds00000,00111,11001 and verifies all radius-one decodings. This additional channel model is not the original noisy-observation model. A perfectly transmitted but false task label remains false: codeword integrity is not task truth. NO-GO for presenting coding alone as intent inference.

## Protocol/reference experiment and post-compiler failure boundary

`inventor_protocol.py/json` uses the unchanged four-box primitive and h=.2s. Two compiled1mm displacement events at.22s and.23s give q(1.5s)=2mm. The exact piecewise-linear reference jerk is checked at every knot; its peak is77/160m/s³, below the unchanged7.5m/s³ guard budget. The simpler sum bound is.5m/s³. These are exact reference calculations; the existing executable guard and plant are not rerun.

If the original±.2mm tracking tube holds for that duplicated history, every physical position at the deadline is at least.8mm away from the intended1mm target. This shows that admissibility of reference dynamics and faithful implementation of a task are separate obligations. Replaying an absolute REVISE through a correct current-goal compiler might instead produce zero additional displacement; that is not the failure being claimed.

The small reducer trace records ADMITTED, ADVISORY_ONLY, DUPLICATE_ACK, CONFLICT_REJECT, STALE_REJECT, and FAILED_REQUEST_PENDING_OLD_TAIL. Duplicate identity with changed payload is rejected; advisory data does not advance the goal; stale epochs do not overwrite current intent. The final rejected new request is a failed task request, never a successful hold. This reducer illustrates obligations, not a production protocol: session generations, restart persistence, authenticated authority, actuator transport, scheduler timing and clock correctness remain unverified.

A useful next certificate should bind accepted revision identity through compilation, queueing, and actual history append. Otherwise an at-most-once receiver can coexist with duplicated downstream effects. Persistent reference history must survive recovery alongside command identity; clearing state on restart is outside the source theorem and can silently violate the old-tail premise.

The delayed20mm reference example retains the original deadline1.5s. With actual execution1.3s, F(1)=1/24 gives reference5/6mm at the deadline. Conditional on the unchanged tracking tube, goal error is at least569/30mm. This is a concrete failure when the source timing premise is violated, not a lower bound on all possible controllers or a claim that every earlier-than-tail deadline is impossible.

## Primary biology reading and boundary

Read the abstract, introduction, and selected results of [Miall et al., 2007, Disruption of State Estimation in the Human Lateral Cerebellum](https://journals.plos.org/plosbiology/article?id=10.1371/journal.pbio.0050316). Their stimulation results were consistent with disrupted predictive state estimation during reaching. This motivates examining command-based prediction of state; it does not establish a robot protocol, infer future task intent, or explain tremor. The proposed execution ledger is an engineering analogy, not a neural-mechanism claim.

## Kernel evidence and verification limits

`inventor_duplicate.lean` instantiates the unchanged P/F0 source formula and proves the duplicated deadline reference, the conditional≥.8mm goal error, failure of the0.2mm success predicate, robust-reference exactness, and injectivity of a goal encoder under the universal full-tube premise. `inventor_verification.py/json` compares P/F0 definition bodies against the original `certificate-03/builder/Kernel.lean`, records source hashes and toolchain, and audits the displayed axioms. The source plant theorem is not imported or re-proved; the tracking tube is explicit in the failure implication. No physical extrema reachability is assumed.

The first Lean invocation failed because its relative file path was interpreted from the Lean working directory. The corrected absolute-path invocation compiled successfully; this was a path failure, not a mathematical failed proof. No approved Challenge file was edited.

## Recommendation and quality

GO for a bounded end-to-end command-identity certificate: one accepted revision maps to one authorized reference-history effect, carrying its exact target and actual schedule. Test post-compiler duplication, stale delivery, conflicting same-ID payloads, restart loss, and deadline failures before connecting the existing tracking theorem. HOLD any claim that protocol integrity establishes true intent, that arbitrarily small motion is certified, that this handles mid-motion replacement, or that the original benchmark endpoint-rest requirement is proved.

Evidence levels remain distinct: finite exact arithmetic; isolated kernel lemmas; unverified protocol implementation; no hardware or new plant result. Quality: faithfulness4/4, reproducibility4/4, discriminatory value4/4, critique4/4, actionability3/4 =19/20. Subjective confidence is high in these bounded deductions; no publication novelty claim.
