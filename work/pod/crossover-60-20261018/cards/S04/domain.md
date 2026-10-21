# S04 domain review: coverage and model-bound acceptance

AI-authored domain research. Runtime: inherited root model; exact identifier unavailable.
Only campaign `domain*` artifacts were created; original research and approved challenges are unchanged.

## Original question and trusted boundary

Can a certificate checker reject incomplete coverage, changed model semantics and stale artifacts without trusting the producer? The source lean-controls README expressly distinguishes generated witnesses from verified results, kernel statements from physical correspondence, and source inventory from a parser. The source-attribution challenge already repaired an earlier incomplete coverage checker. This review does not present that repair as new.

Inspected original scripts: `scripts/verify_project.py`, `verify_benchmarks.py`, `sync_audit.py`, `check_audit.py`, `check.sh` under `/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls`; and `check.py`, `model.json`, `results.json` under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution`.

The project runner executes five fixed steps, records their exits/log hashes, compares selected source hashes before/after, and binds benchmark and uncertainty manifests. Benchmark verification regenerates exact source, appends axiom prints, calls Lean, compares returned declaration sets/axioms and generated-source bytes, then records hashes. Trusted components include the verifier programs, Python/Fraction or Lean implementation, imported dependencies and runtime resolution, filesystem/run integrity, and the reviewer-selected formal statement. Neither a JSON model label nor a successful proof establishes physical semantics.

The source-attribution CLI pins model bytes; `verify` additionally pins producer hash, exact stage/sign/objective/action sets, each branch's inequalities, feasible witnesses, dual/Farkas certificates, summary extrema, action decisions and held-out summaries. Its Python assertions must remain enabled (CLI explicitly rejects `-O`). Imported `verify` is not a self-contained model-byte or interpreter-mode guard; callers must preserve the CLI preconditions.

## Transfer: semantic cover instead of label count

The useful mapping is from finite branch certificates to a quantified model domain. An accepted list must cover every admissible world, each actual world must map into the checked branch semantics, and every such checked branch must establish the desired property. Label presence and counts cannot supply either semantic bridge.

`domain_coverage.lean` proves seven declarations:

1. Semantic cover plus per-branch property implies global property.
2. Explicit actual-branch to checked-branch refinement composes with that cover.
3. Two labels can both certify only `w=false` while the admissible Boolean world `true` remains uncovered.
4. Equality of the checked and required artifact transfers a property of their common decoder; the decoder/byte equality must actually be justified elsewhere.
5. The same artifact can occur at distinct epochs. Content equality alone cannot establish temporal freshness.
6. Source-bound leakage completeness: if `q=λd` and `lo≤λ≤hi`, then either `d≥0, lo*d≤q≤hi*d`, or `d≤0, hi*d≤q≤lo*d`.
7. Conversely, that union entails existence of such a λ when `lo≤hi`, including `d=0` (which forces `q=0`).

The last two are an exact real-arithmetic justification for the source checker's sign-polyhedron representation, not a proof of the full Python checker. They preserve the common leakage variable rather than replacing it with independent per-measurement parameters. Their remaining use requires all other prior and observation rows to be preserved. The fixed source prior `[1/5,3/10]` satisfies the order hypothesis.

The first five declarations use no axioms; the leakage pair uses only `propext`, `Classical.choice`, `Quot.sound`. Local compile exit0 is recorded in `domain_coverage.log`; independent replay was requested. The root ctrl toolchain is used, not the original source project's newer pinned environment. No full source project rebuild is claimed.

## Exact positive and negative tests

`domain_mutations.py/json` imports the original verifier, independently checks pinned model bytes, and preserves originals. Its positive case checks 56 endpoints, one infeasibility certificate and eight actions. Seven rejected mutations are: deleted stage; same-count renamed stage; both sign labels retained but negative branch replaced by positive branch; same-count objective replacement; deleted action; stale producer hash; stale model hash. In particular, the duplicate positive branch fails the regenerated exact-constraint check, establishing a meaningful existing defense beyond set counts. The direct source CLI also passes, recorded in `domain_source_check.log`.

`domain_inventory_test.py/json` invokes the original inventory function on a separate valid Lean fixture. It inventories only `plain_public`, omitting a whitespace-indented public theorem and an attribute-prefixed public theorem. `domain_inventory_lean.log` verifies that all three declarations actually exist and have no axioms. Parent independently found the same pattern; this is corroboration, not a second discovery. A targeted current-source scan found no instances of those two simple patterns; it is not a parser-completeness audit or evidence of an unsafe existing theorem.

This omission is faithful to the tool's documented limitation, but matters if a consumer upgrades 'all inventoried declarations audited' to 'every public declaration audited'. Updating an inventory using the same incomplete recognizer does not close the gap. An independent expected theorem set, compiler-environment export, or a deliberately restricted/rejected source grammar would supply a stronger acceptance boundary. The toy contains only valid safe proofs; no forbidden axiom or admitted proof was introduced.

## Limits, decision recommendation and next test

GO for a bounded acceptance-manifest implementation: fix the required root statement and branch semantics independently of producer output; consume immutable input bytes; reject missing dependency obligations; attach exact source/model/toolchain/policy identities; and distinguish content validity from externally specified freshness/epoch policy. Parent and other roles own race/TOCTOU tests; those are not claimed as domain experiments here.

The kernel results prove composition and the actual two-sign leakage representation. They do not verify SHA-256, filesystem atomicity, Python parsing, complete current theorem inventory, trusted timestamps, runtime provenance, or source-model-to-physical correspondence. Full verification must not accept an empty selected question or replace expected obligations by whatever the producer happened to emit.

Next discriminating test: a private staged snapshot containing an independently fixed complete expected declaration/branch set must reject both syntactic inventory omissions and same-count semantic branch substitution before reporting verified. Preserve a positive exact replay, and require semantic hash policy changes to invalidate the prior result. No project integration was performed, so repository-wide checks are the parent's campaign handoff responsibility; role Python checks are scoped to these new scripts.

Quality: 18/20 (faithfulness4, reproducibility4, discriminatory value4, critique3, actionability3), 90%. Subjective confidence: high in the bounded source and Lean results; no numerical confidence assigned to whole-program or physical assurance.

## Last-mile supplement

`domain_original.lean` adds a direct original-parameter conclusion: for every real `w,d,λ` with `lo≤λ≤hi` and the unchanged `rows w d (λ*d)`, the branch-checked property holds at that same `w,d,λ*d`. This exposes the exact parameter quantification and avoids interpreting label coverage as a semantic proof. The predicate here depends on λ only through q=λd, as do the source's bounds/actions. A property that depends separately on λ needs a correspondingly richer statement.

The reverse branch-to-model equivalence genuinely needs a nonempty interval. At `d=q=0`, the positive polyhedron is satisfied even with `lo=1, hi=0`, but no λ exists. The separate `empty_interval_counterexample` proves this, and `frozen_leakage_interval_nonempty` proves a witness for the actual `[1/5,3/10]`. The forward original-model acceptance is valid even for an empty interval but then vacuous; it must not be used to claim an admissible world exists. Source Python separately demands at least one feasible branch before accepting an action.

Final local status: ten mathematical declarations compile exit0 with allowed axioms; the root inventory fixture was independently compiled in `domain_pm_inventory.log`. `domain_zero_boundary.py/json` checks the actual baseline world `(w,d,q)=(1,0,0)` is in both sign branches and excluded by the separating observation in each. Coverage need not be disjoint; counting shared worlds twice is irrelevant to universal safety (and would be inappropriate for a probability claim). Scoped Ruff passes all three role scripts. Source and artifact hashes are in `domain_acceptance.json`; it is provenance metadata, not an independently trusted certificate. Independent replay remains owned by the critic.

## Full literal source-certificate kernel replay

At the PM's request, `domain_generate_bounds.py` serialized the fixed original certificate set into `domain_source_bounds.lean`. It pins model bytes, runs the original exact verifier, compares every branch's literal constraint set to `expected(model,stage,sign)`, and emits independent Lean proof obligations. The generated statements retain every reported row, including redundant rows. Each of the seven feasible stage/sign branches has four objectives with lower/upper bounds: 56 universal real bounds total. Each bound also has a literal attaining witness satisfying all branch inequalities, the objective equality, and an explicit λ in `[1/5,3/10]` with `q=λd`: 56 attainment declarations. The eighth branch is proved infeasible. All 113 declarations compile exit0, each using only standard allowed axioms; `domain_source_bounds_acceptance.json` records the local audit. Together with the ten coverage/original-parameter lemmas, this role has 123 accepted mathematical declarations, not 123 discoveries.

`domain_source_bounds_binding.json` records source hashes and each statement's stage, sign, objective, endpoint and witness. This is an untrusted serialization manifest; Lean does not prove its JSON-to-source translation. Independent comparison to the original source and frozen question remains necessary. No claim is made that all eight action decision summaries or held-out summary logic have been reimplemented in Lean here. The earlier Python checks cover them at their own evidence level. The source module's first attempt lacked the real-number import and failed; `domain_source_bounds_attempt1.log` is retained. The successful file is frozen for independent replay.

The negative control `domain_source_bounds_negative.lean` changes only the separated positive-branch wheel lower conclusion from `27/70` to `1`; Lean rejects it (exit1, `domain_source_bounds_negative.log`). The accepted lower-attainment witness `(27/70,5/7,3/14)` independently shows why that strengthening is false. The intentionally rejected test file is not an accepted proof artifact.
