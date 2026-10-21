# S04: Complete model-bound certificate acceptance

**PM: GO for a bounded consumer experiment.** AI-written; original question unchanged:
Can a certificate checker reject incomplete coverage, changed model semantics and stale
artifacts without trusting the producer?

The source-attribution checker already rejects missing stage, branch, objective and action
sets. That prior repair works in the reproduced fixed example. The new path is to combine
semantic branch coverage with immutable byte capture and a separate trusted use-context
contract. Labels, hashes and a previous `verified` status do different jobs.

## Provenance and prior work

Frozen sources are the lean-controls README in `/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/`
and the source-attribution `challenge.txt` under
`/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/`.
Their frozen hashes are in roster.json. We inspected the actual checker, model, results,
project verifier, benchmark verifier and inventory scripts; source hashes are in the role
manifests and pm_expected.json. Existing model-change/producer controls were prior work,
not invented in this session. This review concerns artifact acceptance, distinct from S12's
static action geometry.

## Three transfers and their falsifiers

1. **Transactions and immutable snapshots.** Treat proof inputs as one checked value,
   not a path reopened at different times. Preserve exact bytes through hashing, parsing,
   checking and the returned receipt. A deterministic interleaving is the falsifier.
2. **Semantic coverage from model checking.** Required labels must correspond to a cover
   of original worlds; prove the bridge. Preserve q=λd and the common λ interval. Two
   copies of the positive branch have both labels but miss negative worlds. A cover may
   overlap: d=q=0 belongs to both source sign branches.
3. **Unexpected transfer from moment matching and indistinguishability.** Two disjoint
   eight-case sets have the same count and moments through degree3 (8,60,620,7200).
   Aggregate summaries cannot certify coverage. Two epochs can also have identical proof
   bytes: freshness requires external context, while valid same-model proof reuse is sound.

## Experiments and results

- Original exact checker passes56 endpoint certificates,1 infeasibility certificate and8
  action evaluations. Domain's seven omissions/replacements fail as expected.
- Actual source checker's split hash/parse read accepts changed descriptive semantics under
  deterministic read interception; stable changed bytes fail. No claim the saved historical
  run raced, or that the fixed arithmetic became false.
- Actual benchmark/project orchestration code, with **all subprocesses mocked**, records a
  later model hash than the producer consumed; a before/after guard catches persistent
  changes but misses A→B→A. Preflight exception can leave an old verified marker. The
  caller still sees failure; only a status-only consumer confuses attempts.
- Root's first immutable-byte wrapper failed two independent critic tests: mutable mapping
  lookup and certificate bytearray mutation. Failed version preserved. Repaired wrapper
  copies exact plain mappings once, requires immutable certificate bytes, checks fixed
  checker/model identity and reruns arithmetic. Twenty harmful cases reject, five benign
  transformations pass, and four additional critic input/identity attacks reject. Captured
  old bytes remain correctly bound when the caller later changes its mapping.
- Actual inventory extractor misses valid indented and attribute-prefixed declarations;
  Lean compiles all three fixture declarations. This is its documented limited syntax,
  not evidence of an omitted unsafe theorem in the original repository.
- A deliberately disallowed axiom fixture demonstrates benchmark log-parser overwrite.
  Lean correctly reports the forbidden dependency; fake empty output causes the benchmark
  parser to replace it. **The original whole-project audit rejects that same output.**
  This requires generated-source control, not demonstrated access through the current
  JSON-only producer. The negative theorem is never accepted or counted as proved.
- Domain produced10 supporting Lean declarations: exact two-polyhedron leakage cover and
  converse, original-parameter composition, and empty-interval/freshness counterexamples.
  A further113 source-specific statements check56 universal real bounds,56 attaining
  original-model witnesses and1 infeasible branch. A strengthened false bound is rejected.
  Compiler results, independent replay and literal binding are recorded separately.

## Independent critique and acceptance limits

All promoted results require independent replay; see critic.md and its machine-readable
files. The wrapper still trusts Python, approved checker/model semantics, expected hashes,
and private local storage. JSON status is not a portable proof. A nonce alone is forgeable
by its producer and cannot prove fresh measurements. The exact source-to-Lean serialization
is inspected and separately checked, not itself kernel verified. No physical robot, general
hostile-code sandbox, full Python correctness theorem or novelty claim is supplied.

Primary-source checks: [SLSA1.2 verifier/subject/policy model](https://slsa.dev/spec/v1.2/verification_summary)
and [Lean axiom reporting](https://lean-lang.org/doc/reference/latest/Axioms).
These support the established trust distinctions, not a claim that this mechanism is new.
Actual kernel fixtures use pinned Lean4.33.1; current documentation is conceptual context.

## Decision and next action

GO: after all60 initial reviews, spend one30-minute block on a consumer-owned obligation
manifest and immutable fixed-model snapshot adapter, with20 prefrozen held-out/mutation
cases, proper source-bound kernel acceptance, and explicit invocation receipt semantics.
Require one independently reproduced accepted case plus rejection of coverage, identity,
mutable-input, stale-attempt and audit ambiguities. Do not integrate until repository checks
and source binding pass. See next_block_protocol.json.

Quality:19/20 =95/100 (faithfulness4, reproducibility4, discrimination4, critique4,
actionability3). Subjective confidence: high for the scoped reproduced failures and exact
mathematics; production adequacy, physical applicability and novelty unestablished. This is
not a calibrated success probability. Ten minutes reviewed is not ten minutes proved.

Final independent acceptance:125 mathematical/helper declarations (10cover/bridge +113source certificates +2original-action theorems); three trivial syntax fixtures separately. Root theorem directly certifies c=-1/2 for original real λ and allρ∈[0,1], and supplies a valid rejecting witness for c=-1. All printed closures permitted. This is scoped static model assurance, not whole Python acceptance.
