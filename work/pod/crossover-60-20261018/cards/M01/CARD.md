# M01 — extend the saved 6-by-4 square-sum grid

AI-written crossover research. PM gate: **GO for certified candidate filtering**, with global extension/nonextension **HOLD**. No fifth column was found. This card becomes a completed timed review only when `state.json` records `reviewed`; timestamps and conservative gap exclusions are authoritative there.

## Frozen question and provenance

Can the saved rational 6-by-4 square-sum grid acquire a fifth distinct column, yielding five distinct integers whose factor-difference sets share five differences? Sources: original `work/pod/885/FINDINGS.md`, parent `work/pod/README.md`, and `work/pod/885/extend_6x4.py`. The first two changed since selection; snapshots and hashes are recorded in `source_drift.json`. The question and roster were not changed. Current source notes report bounded negative searches through denominator one million; that execution claim was not freshly certified here.

The two classes use

- N₁=[206222625,677376000,2019635200,4786481700,16670745700], known differences [13440,75936,129360,279840].
- N₂=[10046592,24561225,115706752,281637972,564578560], known differences [5976,10104,24216,69624].

We seek positive reduced w=p/q, distinct from the four known differences, with all five w²+4Nᵢ rational squares. The zero row supplies w² automatically. Multiplying by q² yields positive integers Nᵢq² and five distinct integer differences qd₁,…,qd₄,p. Neither changing sign nor repeating a known column counts. All 48 grid entries and 40 positive factor witnesses were independently checked.

## Creative transfers and break conditions

1. **Quotient-first constraint solving.** Elliptic group operations preserve selected square constraints, while explicit lift certificates retain the others. Domain uses y²=x(x+4N₁)(x+4N₂); inventor uses Y²=∏ᵢ₌₁³(X+4Nᵢ). These are different quotients. A curve point is insufficient without every residual square, positivity and distinctness condition. Exact counterexamples expose that failure.
2. **Unexpected coding/finite-state transfer.** View residual square classes as correlated error-detecting checks and pull them back to coefficient residues in a finite elliptic group. This can reject coefficient combinations before large rational arithmetic. It uses good reduction and must retain infinity. It contains the same local information as direct congruence checks; it is not independent evidence or a new general descent theorem.
3. **Branch-and-bound from integer gaps.** Eliminate the shared numerator between two factor equations; adjacent integer roots give exact exclusion certificates. This changes the admissible numerator growth from the naive O(q²) bound to O(q^(4/3)). It does not bound q globally. Equality, reducedness and positive-factor assumptions are essential.
4. **Localization cycle consistency, deliberately challenged.** Additive row-difference cycles telescope for any proposed X, including failed rational lifts. NO-GO as an extra arithmetic discriminator by itself; useful only for representation audits.

## Tests and results

**Exact quotient tests.** Domain generated 32 declared doubled candidates across both classes; all satisfy the two encoded nonzero-row conditions and all fail each of the remaining three rows. Ninety-six consecutive-square rejection certificates were independently replayed. Two Lean identities justify the partial lifting formulas. Inventor tested 32 operations on class 1, producing 28 distinct finite X values; the three complete lifts merely repeat old columns. Sixteen chord/root certificates were independently checked. The exact relation P₁=P₂+P₃ removes a redundant supplied direction but establishes neither rank nor a complete generator set.

**Finite-state discriminator.** At prime 197, the first-class curve has 204 points; supplied points generate a 51-point subgroup. Logs relative to P₂ are (42,1,41,39). Necessary complete-lift coefficient states for mP₂+nP₃+rP₄ are

    (m+41n+39r) mod 51 ∈ {0,1,9,10,12,39,41,42,50}.

This excludes 42 of 51 coefficient states exactly. Successive gates retain 204→51→25→15→9 points, including infinity. Prime 197 was selected after the discovery pool, then frozen for a six-new-candidate holdout, all rejected. These counts are not general performance probabilities. A direct projective-w test retains nine of 198 states and carries the same local information. Independent checker replayed curve enumeration, logs, certificates and candidate reductions.

The concrete partial lift Q=2P₂+P₄−P₃ has X,Y denominator valuations 2,3 at 197 and reduces to (0:1:0). It is not a complete column. This demonstrates why affine-only filtering is unsound even for finite rational points. Dropping infinity and admitting an invalid coefficient state are rejected controls.

**Overflow audit and arithmetic repair.** The historical C++ column search squares unchecked uint128 numerators; overflow occurs within its reported range. Let P₀=18446744073708551616. For q≤10⁶, every column discriminant with p≤P₀ fits uint128. Any candidate with p>P₀ forces the enumerated factor a into eleven first-class branches or one second-class branch. Exact adjacent-factor gaps reject all twelve using another original row. Independently compiled Lean lemmas prove these exclusions, the safe bound, the factor caps, and their composition for valid two-row factor equations. A threshold-zero mutation fails with an exact rational root; an enlarged-denominator known-column example violates the conclusion when q≤10⁶ is removed. Original execution coverage, all enumeration semantics, rational-root/parity conversion, and row searches remain separate obligations. We did not rerun or modify the original search.

**All-denominator reduction.** For positive integers A<B and factors a,c, elimination gives q²(Ba−Ac)=ac(c−a), with a<c<Ba/A. Writing g=gcd(A,B), every valid candidate obeys

    a³ > A²g q²/[B(B−A)],    p³ < AB(B−A)q⁴/g.

The strongest row-pair constants in the two classes are 397977541714368000000 and 14739018868537891200. A sharper fixed-a condition is q²≤aL(L−a)/(Ba−AL), L=ceil(Ba/A)−1. Equality must survive. Reducedness also restricts squarefreepart(a) to divisors of rad(A), giving 32 or 16 branches for the chosen enumeration bases. Each branch remains unbounded. Producer checked 20,765 toy candidates/722 valid pairs; independent critic checked 181 valid pairs and 149 reduced square-class cases, plus equality and unreduced controls. Three Lean lemmas prove conditional elimination/bracket algebra; integer-floor, gcd, square-class and cubic bridges remain hand-derived.

## Evidence, critique and decision

Root and independent critic reproduced all promoted proof files: **23 distinct Lean declarations**, standard propext/Classical.choice/Quot.sound only. `pm_lean_replay.json` binds source hashes and logs. No approved challenge, original research file, public CLI or physical robot was changed. Exact Python arithmetic and finite enumerations are separately labeled; they are not Lean proofs of complete search coverage. General good-reduction/descent facts and novelty have not been newly formalized or established. Primary-source checks and unavailable official status are recorded in `pm_sources.md`.

**GO:** after all 60 initial reviews, one 30-minute block on a faithful coefficient/gap filter adapter. Declare the second-prime selection rule and at least 20 fresh coefficient/factor cases before generating them. Test classes admitted by prime 197; verify good reduction, preserve infinity, handle a noncyclic second group if encountered, and measure joint survival without assuming independence. Every survivor still needs exact full lifting and distinctness. Include known positives and mutations of infinity, equality, reducedness, denominator bounds and factor-to-original-question binding. Require a discriminating reduction or a useful failure before renewal. No blind denominator expansion.

**HOLD:** global rational-point completeness, saturation/generator completeness, fifth-column existence or impossibility, original bounded execution certification, and novelty. NO-GO for bare quotient points, cycle equations alone, duplicate columns and interpreting zero hits as a global theorem.

Quality rubric: faithfulness 4/4, reproducibility 4/4, discriminatory value 4/4, independent critique 4/4, actionability 3/4 = **95/100**. Subjective confidence is high in the scoped certificates; eventual extension success is uncalibrated. Root PM plus domain `inventory_math`, inventor `inventory_vision_robotics`, critic `inventory_controls_safety` used the inherited working model; exact runtime identity unavailable. No model-family diversity or Spark inference is claimed.
