# S04 — complete acceptance, snapshot binding, and freshness

AI-written inventor review. Inherited exact model identifier unavailable. Root owns the ten-minute clock and PM decision. Originals were read only; own writes are `inventor*`.

The concrete finding is a conditional snapshot race in the original source-attribution checker's entry point: it hashes one read of model.json, then parses a second read. An isolated controlled interleaving passes the pinned-hash check on approved bytes while parsing changed bytes. The stable changed file is rejected. This is an acceptance-boundary weakness under mutable concurrent storage, not evidence that the historical saved run raced or that its original mathematical bounds are false.

## Sources and existing protections

Read the frozen S04 card; `/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/README.txt`; its `scripts/verify_benchmarks.py` and `scripts/verify_project.py`; and the original adjacent-controls `source-attribution/challenge.txt`, `check.py`, `model.json`, and checked results.

The source-attribution checker already requires exact stage, sign-branch, objective, and action sets. It rechecks nonnegative dual certificates and feasible witnesses, prevents empty-set acceptance, checks held-out summaries, and pins model bytes in main. Its source SHA256 is `33e2021e49f95c9b2ea433db7814681458f2c575ea17243b2f4ab58780b8f400`. It does not merely trust the producer's declared counts.

The Lean-controls family distinguishes proof generation from verification, regenerates sources, checks them, audits allowed axioms, and records hashes. Its JSON model description is metadata; the README explicitly locates the semantic bridge in Lean model identities. A JSON hash alone must not be described as proving physical semantics. The critic independently investigates the orchestration-level model-read and ABA races; I avoid duplicating those experiments.

## Transfer1: database snapshot isolation / transactional acceptance

Map a verification run to a read-only transaction over the authoritative model, case universe, proof artifacts, semantic dependencies, and policy. Preserve one coherent version of every input from parsing through checking to the emitted receipt. A successful receipt must identify the bytes actually consumed, rather than bytes reread later from the same path.

A content digest identifies bytes, not a continuously stable pathname. Pre/post digest equality also does not by itself prove no intermediate version was consumed. Immutable snapshots, captured buffers, or an independently controlled checkout are ways to establish the stronger requirement; they are different implementation choices, not automatic consequences of hashing.

**Executed source-bound discriminator.** `inventor_snapshot.py` executes the unchanged original checker from captured source bytes in an isolated module. It intercepts Path reads in memory; it does not modify any original file or invoke the producer. Three cases:

1. Approved bytes for both reads: PASS56 exact endpoint certificates,1 infeasibility certificate,8 action evaluations.
2. Changed bytes already present for the hash read: rejected as a changed predeclared model.
3. Approved bytes for the hash read, changed bytes for the parse read: the same PASS output occurs.

The changed bytes replace the textual relation with `q=lambda*d+1` and the wheel-gain statement with gain2. The arithmetic checker still reconstructs its fixed original semantics. Therefore this mutation does **not** prove a false rational inequality was accepted. It proves that the entry point's promised byte pin can be bypassed by a split-read interleaving, and that a parsed semantic description can then differ from the actual fixed arithmetic interpretation. The mathematical interpretation remains the checker code, not those free-text fields.

The exact read trace and hashes are recorded in `inventor_snapshot.json`. A proposed repair boundary is also tested: read the model bytes once, check that buffer's digest, and parse that same buffer. This rejects the changed snapshot. It does not by itself fix races in dependencies, output files, or later receipt consumers. If the model storage is already trusted immutable for the whole run, the demonstrated race is outside that threat model; state that assumption explicitly.

**Falsifier for the next adapter:** inject a model replacement after the approved hash read, and require either rejection or verified parsing of the captured approved snapshot. No accepted receipt may name changed bytes as though they were checked. Keep the original failing test as evidence rather than silently replacing it with the repair.

## Transfer2: indistinguishability / externally anchored freshness

A deterministic checker receiving identical bytes and identical trusted context must return the same result in two worlds, even if one world calls those bytes current and the other calls them stale. Thus a standalone artifact cannot certify its own freshness relative to unobserved external state.

`inventor_coverage_freshness.py` constructs two such histories. A model-bound receipt at epoch17 is locally identical whether authoritative current epoch is17 or18. Adding an independently supplied expected epoch rejects the unchanged replay in the second history. But an untrusted producer can relabel an unchanged proof with epoch18: the label does not attest that mathematical generation occurred anew.

The acceptance policy must distinguish at least three things:

- **Mathematical reuse:** an older proof remains valid for exactly the same current theorem and dependencies. Fresh generation is unnecessary.
- **Current-context binding:** the accepted proof must match the authoritative current model, observations, required cases, and policy. Their identity comes from outside the producer and must be bound to what was actually checked.
- **Temporal attestation:** a particular process ran after a specified event or at a specified time. Producer timestamps/nonces alone do not prove this. A trusted verifier can attest its own run, within its clock/runtime trust boundary.

A nonce can prove response-after-challenge only within a suitable protocol; it does not force recomputation of a reusable proof. Likewise, a digest does not show that an observation was recently measured. No impossibility is claimed for an authenticated external context or trusted measurement source—those are precisely the additional inputs needed.

**Falsifier:** replay yesterday's mathematically valid bundle against today's independently supplied expected observation/model digest. It must fail if the theorem context changed; it may legitimately pass if the complete context is identical and policy permits caching. Then change only the producer's timestamp: the decision must not change.

## Transfer3 (unexpected): coverage as a code, and the failure of summary checks

Use independent case identities as the coordinates of an acceptance obligation. Preserve the entire finite domain and the theorem attached to each coordinate. Checking a handful of aggregate statistics is only an error-detection syndrome, not proof of complete coverage.

The exact test supplies disjoint eight-case sets

`A={0,3,5,6,9,10,12,15}` and `B={1,2,4,7,8,11,13,14}`.

They have identical cardinality, sum, sum of squares, and sum of cubes: `[8,60,620,7200]`. A checker that accepts those four summaries accepts a bundle omitting *every* required A-case. Exact comparison to the independently derived expected set rejects B. This is a deterministic arithmetic counterexample, not a probabilistic hash-collision claim.

The original source checker already uses exact expected sets before its final count assertion, so this test supports its existing design rather than alleging it has this weakness. A cryptographic hash of an independently fixed canonical case manifest can be a practical identity check under its explicit collision-resistance assumption. A producer-supplied expected-manifest hash merely asks the producer whether it met its own reduced obligations.

Do not require a different proof object for every case merely to force a bijection: one theorem may legitimately cover several cases. What must be complete is the checked mapping from every required case to a proof of that case's actual proposition. Reusing a valid theorem is sound; relabeling a proof about a different branch is not. Overlapping branch boundaries also need not be disjoint if the full union and all assumptions are preserved.

**Falsifier:** preserve proof counts and numerical summaries while replacing required case identities, then separately preserve identities while exchanging the branch assumptions underneath one proof. Both must be rejected by the corresponding coverage and semantic-binding checks.

## Recommendation and next experiment

Recommend GO for an isolated immutable-snapshot acceptance adapter, retaining the current source checker as the mathematical backend. The next bounded experiment should:

1. Capture authoritative model bytes and expected case universe once from a trusted context; parse only that snapshot.
2. Bind every certificate to its exact reconstructed branch constraints and objective, then call the unchanged mathematical checks.
3. Emit a receipt naming the captured inputs, policy, checker/dependency identities, and independently supplied expected context identifier only after all checks succeed.
4. Inject replacement between hash and parse, missing required branch, proof-to-branch reassignment, stale authoritative context, and producer-only timestamp changes.
5. Have an independent consumer recheck the receipt's current expected context and complete case binding.

This is a concrete next test, not a request to edit the original research sources now. It does not require trusting the producer. It does require naming trusted inputs and the verifier/runtime/dependency boundary. Freshness without any external anchor is NO-GO; cached valid mathematics is not inherently stale.

Own exact scripts pass. No Lean theorem, cryptographic security proof, physical validation, or live concurrent exploit is claimed. The snapshot harness intercepts reads; it is a controlled interleaving of the real entry-point code. Original sources and all historical results remain unchanged.

Quality rubric: source binding5/5, distinct mechanisms4/4, decisive tests5/5, independent-check readiness2/3, scope discipline3/3 =19/20 for this bounded inventor contribution. Subjective confidence in the reproduced split-read behavior99%; this is not a probability that any prior saved run was affected.
