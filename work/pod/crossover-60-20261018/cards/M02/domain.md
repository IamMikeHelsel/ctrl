# M02 — domain recovery and scoped proof bridges

AI-assisted domain role. Inherited root model; exact model identifier unavailable. Root owns the session clock and PM decision. All work here is isolated under `cards/M02/domain*`; original work/273, Research sources, approved Challenges, and ongoing jobs were not edited.

## Frozen question and source status

Can every finite distinct-modulus prime-minus-one covering be excluded when all moduli are 11-smooth, with exponents unbounded, and what fails at 13-smooth?

Read the current `work/273/research-note.md`, `plan.md`, `check_eleven.py`, `smooth_probe.py`, `probe-11.json`, `probe-11-symmetric.json`, and `lean/Research/Covering{Mass,Tail,CRT,Assembly,Family}.lean`. The current source already proves the **7-smooth** case in `Research.CoveringFamily.seven_smooth_period_gap` / `seven_smooth_not_cover`, for arbitrary finite sets of distinct moduli, arbitrary integer residues, and unbounded exponents. This is stronger than the older roster context; it is prior work, not our discovery. We did not rebuild that full source tree.

The current 11-smooth result is an exact Python capacity computation, not an accepted full Lean theorem. Its extended prefix is (4,6,10,12,16,18,30,36), period720; exponent caps (14,9,6,5,4). Reported search: 5265 retained moduli, 3518 nodes, 3271 prunes, no unresolved leaves, 2614 memo hits. The tail is 1806085527193/7116137582400000. The minimum prune gap is 50661803066306609/1239915812357376000000. The retained finite pool uses bases2,3 Fermat filters; pseudoprimes may remain, which is conservative. A passing filter is not a primality proof.

The 13-smooth candidate report is `work/273/candidates/20261019-052643-273-solve-298c/probe-13-spark.json`: period5040, prefix (4,6,10,12,16,18,28,30,36), pool22944, time limit after about240s, 26952 unresolved leaves. The saved full leaf is [(4,0),(6,1),(10,0),(12,3),(16,2),(18,3),(28,2),(30,2),(36,9)]. Its capacity excess is positive. This is a failure of that relaxation/search to exclude the leaf, not a covering witness.

## What the transfers preserve

1. Product geometric series / partition-function tail: retain every unbounded exponent outside the finite box. Nonnegativity makes the omitted infinite region safely bound any finite chosen subfamily. The transfer breaks if reciprocal weights or parity representation are not bound to actual moduli.
2. Gauge symmetry / group action: simultaneous integer translations preserving old congruence classes reduce the new residue to its gcd orbit. This preserves the actual old and new membership predicates, not just a count. It does not by itself justify memo-state canonicalization or full tree coverage.
3. Finite weak duality: a feasible fractional cover is a certificate that no nonnegative reweighting can make a stated single-class capacity relaxation exclude the leaf. It preserves the relaxation objective; it does not produce integer congruence classes covering all integers.
4. Joint capacities / correlation: maximize the union of two actual candidate sets instead of adding two separate maxima. This never worsens the bound. A positive uniform overlap discount is an additional condition and often fails when all residues of even moduli are allowed, because opposite parity choices are disjoint.

## Kernel-checked isolated results

All successful files were compiled with `lake env lean ../work/pod/crossover-60-20261018/cards/M02/<file>` from `/Users/mike/Dev/ctrl/lean`, using its existing pinned toolchain. Printed axiom closures contain only `propext`, `Classical.choice`, `Quot.sound`. Failed draft logs are preserved and not accepted as proofs. No source theorem or frozen Challenge was changed.

- `domain_tail.lean`: 3 printed declarations. The 11-smooth even-weight product sums to77/32; exact box mass; **every finite subset outside the box**, without exponent bounds, has total weight at most the checker tail. This extends the existing 7-smooth proof pattern, with attribution. Independent critic replay passed.
- `domain_symmetry.lean`: 4 printed declarations. Every admissible prime successor passes the two Fermat filters; every new residue admits a canonical translate below gcd(L,m); shifts by multiples of L preserve all previous classes with modulus dividing L; new-class membership transforms exactly. Independent critic replay passed.
- `domain_crt.lean`: 2 printed declarations. For arbitrary positive B,m, any H divisible by both, and survivor set U, a residue class hits at most H*gcd(B,m)*C/(B*m), provided C bounds every compatible survivor fiber. The period720 specialization follows. This imports the existing `Research.CoveringCRT` compiled dependency and reuses its injective counting proof; original sources were not rebuilt. Independent critic replay passed. U need not be restricted to range B for the upper bound, but exact lifted-survivor cardinality elsewhere requires that restriction.
- `domain_joint_capacity.lean`: 4 printed declarations. Joint pair maximum bounds every actual pair; it is at most the separate maxima; a proved unavoidable overlap gives a discount; strict joint plus remaining budget leaves an actual uncovered point. All candidate families and remaining-budget assumptions are explicit. Independent critic replay passed.
- `domain_duality.lean`: 3 printed declarations. Finite fractional-cover weak duality, its no-strict-exclusion corollary for c≥1, and a grouped-budget version. A group has nonnegative λ[g,r], total≤budget[g], and every member's weighted subset mass≤cap[g]; pointwise fractional coverage≥c then forces c*total weight≤Σ budget[g]*cap[g]. Ordinary residue classes and a singleton tail group fit this statement. The tail group's cap is max survivor weight. There is one harmless unused section-variable linter warning. Independent critic replay passed.

- `domain_representation.lean`: 3 printed declarations. Every admissible 11-smooth modulus has a positive power of2; every finite distinct admissible family has a chosen exponent representation on which the modulus map is injective; the reciprocal of that modulus is exactly the geometric-tail weight. This adapts the source 7-smooth proof pattern. It assumes no exponent cap and no unproved global uniqueness theorem. Independent critic replay passed.

All six independent compile processes exited0; all nineteen printed declarations have permitted axiom closures, with hashes recorded in critic_lean_hashes.json. Nineteen printed declarations across six files, plus elementary helpers, are scoped bridges. They are not a complete 11-smooth exclusion theorem. The PM's concrete 13-leaf rational fractional certificate is **not embedded into these Lean statements**: its finite arithmetic remains separate exact Python evidence pending any later kernel instance. A solver report alone is not accepted.

## Independent exact test

`domain_orbits.py` independently reconstructs canonical translation orbits for the frozen 11-smooth prefix, without importing producer code. It performs95040 pointwise checks across period720: every old residue remains unchanged and the translated new class has equivalent membership. Canonical choice counts are [1,2,2,12,4,6,30,36]. Negative control: with L=4,m=6,a=1, forcing representative0 is invalid; the orbit is {1,3,5}. Result is in `domain_orbits_results.json`. Script passed ruff formatting/checks. This finite test supplements, rather than substitutes for, the universal symmetry lemmas.

## Remaining binding obligations

A complete 11-smooth theorem still needs all of the following in one accepted proof:

- The representation theorem takes explicit existential power-product smoothness. If the final statement instead defines smoothness by prime-factor support, prove that equivalence too. Connect the now-proved arbitrary-family representation and reciprocal identity to the tail and finite-pool modules in the final assembly. The constituent representation lemmas alone do not establish the covering theorem.
- Kernel-check all finite-box membership, retained-pool inclusion, exact reciprocal group masses, and the 5265-element table. Prime⇒Fermat is now proved, but table completeness is not.
- Bind exact integer denominator scaling to rational bounds; establish that every scaled quantity has the claimed denominator divisibility. Python `int` truncation is safe only under that invariant.
- Verify every tree branch and pruned leaf, plus symmetry and memoization correctness. Canonical shifts preserve every prior class and hence the whole survivor set. Memoization by (depth,U) additionally needs the fixed remaining pool/list semantics; strict depth increase excludes an unfinished same-key ancestor in serial DFS. Canonical translation is proved, but the serialized tree/DAG checker is not.
- Augment an arbitrary family with any missing prefix moduli using arbitrary residues. All eight prefix successors are prime, and exclusion of every augmented family implies exclusion of the original family. Then combine conditional CRT capacities, the unbounded tail, prefix classes, and an arbitrary common period H; prove lifted survivor cardinality with U⊆range720.
- Faithfully normalize arbitrary integer residues and transfer the uncovered natural-period representative back to the original integer classes.
- Connect the final theorem to an approved statement if promoted into the primary solution workflow. Nothing here solves unrestricted Erdős273.

## Recommendation and next test

Recommend **GO** for the 11-smooth certificate-to-kernel bridge: the universal tail, symmetry, and CRT pieces now have checked support. Precise next action is export the existing small pruned tree plus exact finite group-mass table, verify its node semantics and coverage recursively in Lean, then assemble arbitrary finite families. Keep the full 11-smooth claim on **HOLD** until that assembly is accepted.

For the saved 13-smooth leaf, a verified fractional certificate with c>1 would justify **NO-GO for nonnegative reweighting of the same single-class relaxation**, while preserving GO for genuinely stronger joint-capacity or residue-coupling tests. Do not interpret this as a NO-GO for the mathematical conjecture.

Quality grade for this domain contribution: **17/20 (85%, B+)**: exact source recovery and reusable checked bridges, but no finite-certificate kernel instance or complete family theorem. Subjective confidence: **97%** in the stated scopes after independent replays; this is not a probability that the full 11-smooth theorem is proved. PM owns the final campaign decision and grade.

A possible certificate-serialization improvement, not yet tested here: downward-round every fractional λ to denominator10^6. This preserves group budget inequalities, while each survivor loses at most (number of gcd groups+1)/10^6 coverage, since at most one residue coefficient per group and one singleton tail coefficient contributes. If the claimed c≈1.086312 is independently accepted, the margin may permit a much smaller fixed-denominator certificate at c=27/25. Preserve the original certificate and independently recheck the rounded one before promotion.

At the PM stop boundary, an attempted `domain_round_certificate.py` test failed before arithmetic checks because `tail_multipliers` is a list, while the draft reader assumed a dictionary. No rounded certificate or accepted rounding result was produced. The script itself passed ruff and was formatted, which does not validate its runtime behavior. Preserve it as a failed first attempt; fix the schema only in a later authorized continuation block. All accepted Lean modules remain unchanged.
