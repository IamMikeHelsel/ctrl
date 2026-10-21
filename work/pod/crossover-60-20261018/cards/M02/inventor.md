# M02 cross-discipline inventor

AI-written initial review; inherited root model, exact identifier unavailable. Only inventor-owned campaign files changed. No Spark job, original script execution, or live273 artifact edit.

## Original question and source binding

Can conditional residue capacity exclude every finite distinct-modulus prime-minus-one covering in the eleven-smooth family, and identify why the thirteen-smooth extension fails? The frozen roster predates some current evidence. `work/273/check_eleven.py` independently replays the11-smooth Python calculation:5265 retained moduli, period720,3518 visited nodes,3271 pruned, and positive minimum density margin50661803066306609/1239915812357376000000. This role inspected that source and `probe-11-symmetric.json`; it does not claim to have kernel-checked that result. The source's seven-smooth formal theorem is a separate restricted-family result, not a solution of273.

The saved13-smooth file is `work/273/candidates/20261019-052643-273-solve-298c/probe-13-spark.json`. It stopped at a time limit after89700 visited nodes and26952 unresolved leaves. Its worst recorded assignment is (4,0),(6,1),(10,0),(12,3),(16,2),(18,3),(28,2),(30,2),(36,9), period5040. It is only the worst encountered leaf, not an established globally worst leaf.

`inventor_adaptive.py` independently rebuilds the exponent box, Fermat overapproximation, exact geometric tail, period masks and conditional capacities without importing source functions. Its22944 retained moduli and tail57309026135016113/203244005490926400000 match the saved file. Base2/3 Fermat passes are not called primality certificates: retaining pseudoprimes weakens an upper bound safely. Distinctness is essential because each remaining modulus contributes at most once. Prefix classes can be added to an incomplete proposed family to strengthen its coverage, and all new-residue choices are quantified in each refinement.

## Three transfers and their falsifiers

**1. Abstract interpretation and adaptive partition refinement.** A branch's surviving residues are a finite abstraction of infinitely many integers; grouped conditional capacities overapproximate all remaining congruence classes. Refine a branch by assigning one more modulus, retaining every residue alternative. The global geometric tail still includes all omitted exponent tuples. Because the tested added moduli divide5040, this experiment changes the surviving set but never needs to change the period or the tail. For a new modulus outside that period, this shortcut would be invalid: period and gcd capacities must be rebuilt.

The useful decision statistic is worst child capacity excess, not average improvement or one convenient child. Fixed-smallest-modulus selection can waste work. The falsifiers are a dropped residue alternative, a reused modulus, changed period without reconstruction, or a claimed advantage that vanishes when compared against a fixed sequence at the same depth.

**2. Conditional fractional-cover dual weights.** Interpret a surviving periodic residue's weight as a demand and each possible congruence class's largest weighted intersection as its service capacity. A weighted demand larger than the sum of capacities excludes coverage. Unlike unconditional weights, the prefix has already broken translation symmetry. Nonuniform weights may identify poorly served parts of the surviving set.

The experiment restricts weights to indicators of a residue class or its complement inside the saved surviving set. For these0/1 weights, max(weight)=1 retains the original tail bound unchanged; every retained modulus still uses the exact conditional weighted capacity. A more general weight vector requires multiplying the unconditional tail by its maximum weight, or a separately justified sharper tail. Falsifiers include dropping this factor, using a minimum instead of maximum over the adversary's residue choices, or reducing raw excess merely by shrinking total weight while worsening normalized excess.

**3. Unexpected transfer from duplicate-information fusion: coverage combines by union.** Summed scalar capacities double-count integers covered by two remaining classes, just as duplicate evidence can inflate an information score. Group a small block of moduli and replace the sum of their individual maximum coverages by the maximum coverage of their union. This is an idempotent set operation, not a probabilistic independence assumption. It preserves every choice of the block's residues and leaves all other moduli and the infinite tail untouched.

For moduli dividing the current period, the finite union cardinality directly gives the exact density bound. For a general block its common period must be used. The strongest falsifier is double-spending a modulus in multiple overlap corrections: three identical singleton sets have total individual size3 and three pair overlaps1; subtracting all overlaps would give0 even though their union has size1. Disjoint blocks or correctly constrained fractional block weights avoid that invalid inference.

## Exact experiments

The saved worst branch has1574 surviving residues and exact capacity excess

355965731451484909486943/8853308879184753984000000 ≈0.04020708374.

All added residues are tested for each eligible modulus≤120 dividing5040:40,42,60,70,72,112. None closes this leaf in one step. Best worst-child excesses are:

| next modulus | unique children | worst excess |
|---:|---:|---:|
|42|33|0.02021272152|
|60|27|0.03131624687|
|40|29|0.03666836763|
|72|33|0.03831625218|
|70|60|0.03901281565|
|112|75|0.03925430135|

The adaptive second-level test tries both40 and60 separately on every unique42-child, selecting the smaller worst-child bound. It always chooses60: all33 branches agree. Thus there is **no adaptive advantage over fixed42→60 in this bounded test**. That sequence prunes only1 of891 distinct second-level children, leaving worst excess223417580362732718172257/17706617758369507968000000 ≈0.01261774459. These are local descendants of one saved leaf, not a global exclusion tree or a covering witness.

The indicator-weight test checks71 nonempty class/complement cases. None excludes coverage. Its best normalized result merely reproduces the original surviving set, because complementing an already excluded class changes nothing. Strict subsets do not beat the uniform normalized result in this test. This rejects the tested simple weighting heuristic, not all weighted dual certificates.

The block-union test succeeds modestly. Moduli42 and60 have separate maximum covered counts summing to204, but their joint maximum union has192 elements, attained for residues41 and59. Their block bound therefore saves exactly12/5040=1/420 in density without any branch split. It leaves excess334886424596283114286943/8853308879184753984000000 positive. Another pair70,72 saves only1/5040; the other13 tested pairs save nothing. Exhaustive enumeration of all76 partial matchings on the six candidate moduli certifies that the maximum disjoint-pair improvement is13/5040, attained by blocks(42,60) and(70,72). The resulting exact excess333129815691682964686943/8853308879184753984000000 ≈0.03762771866 remains positive. This is a genuine sharper upper capacity bound but does not close the saved branch. The matching is checked for disjoint vertex ownership; the three-singleton negative control prevents interpreting arbitrary overlap subtraction as valid. No claim of novelty is made for grouping congruence classes.

The entire infinite tail is only≈0.00028197154. Even counterfactually deleting it leaves this branch's original bound positive at353469350273043607604663/8853308879184753984000000 ≈0.03992511219. Deletion would be an invalid certificate; the calculation diagnoses why merely tightening the tail to zero cannot close this particular bound. It says nothing about additional composite elimination or a different geometric abstraction.

## Further discriminating tests during the initial review

`inventor_block.py` tests whether coupling the successful pairs loses more overlap information. It reconstructs the original surviving set, then enumerates all pair choices and discards a mask only when it is contained in a retained mask. For every possible other blockC, A⊆B implies A∪C⊆B∪C, so this is a valid upper-bound pruning rule. The JSON records deduplication multiplicities, maximal representatives and every discarded-mask superset witness.

The four-modulus block(42,60,70,72) has12,700,800 raw residue tuples,1,764,180 deduplicated pair combinations and1,570,816 combinations after certified dominance pruning. Its exact maximum is289, attained at residues(5,23,14,33). This equals the previous pair upper192+97: cross-pair coupling provides **zero additional gain** here. The short certificate is simply the two independent pair upper bounds plus that attaining four-class witness; the enumeration need not be trusted to verify optimality.

Adding the two remaining candidate moduli40 and112 still provides no additional improvement. Their joint maximum is141. The six-modulus union upper is therefore289+141=430, and residues(5,23,14,33,6,10), in order(42,60,70,72,40,112), attain430 exactly. An equality-case check covers2520 maximizing four-block masks and18 maximizing final-pair masks. Thus430 is the exact global union maximum for this six-modulus block on this saved leaf. The improvement remains exactly13/5040. The claim concerns this block with all other capacity terms unchanged; it does not rule out larger blocks, conditioning or another abstraction.

`inventor_lift.py` tests a materially different refinement: modulus52, whose prime successor is53, exposes a13-adic coordinate absent from the original period5040. The period becomes65520; capacities are rebuilt in94 gcd groups using exact residue histograms. Lifting the old surviving set alone, without assigning52, exactly reproduces its old capacity excess. This negative control catches the mistake of treating a representational period change as new information.

Translation by5040 preserves every already assigned class and partitions all52 candidate residues into four orbits, represented by0,1,2,3. All52 residues occur exactly once in the serialized orbit partition. Assigning52 gives respective excesses≈0.03114115,0.03481229,0.03522541,0.03290728, all positive. The exact worst is249489142341143507892211/7082647103347803187200000. The full geometric infinite tail is unchanged. This13-coordinate refinement is weaker than modulus42 on the tested worst-bound criterion, although it has only four canonical children; no computational superiority claim follows without an equivalent-cost benchmark.

## Decision and continuation

GO for a bounded combined test: use block-union capacity to rank candidate refinements, retain exact full-history residue sets, and compare a declared limited candidate set against fixed sequences before scaling. The present useful concrete result is that42 is a better next modulus than40 or52 for the saved branch by worst remaining excess; adaptive branching itself has not earned a benefit claim. The exact six-block witness now makes further coupling of those same six moduli a NO-GO for improving this particular upper bound: it is already sharp. A second GO is to export a small branch certificate whose consumer reconstructs the pool/tail, checks every residue alternative, and checks each block's disjoint ownership, then kernel-check the arithmetic and universal counting bridge.

NO-GO for treating a positive upper-capacity excess as a cover witness, deleting the infinite tail, combining overlapping pair corrections naively, or claiming the small adaptive tree excludes13-smooth coverings. HOLD the universal11-smooth formal extension until the larger tree, tail and statement quantifiers are assembled and audited in Lean. All evidence here is exact Python arithmetic with source reconstruction, not a Lean theorem or external solver certificate.

Quality rubric: faithfulness4/4, reproducibility4/4, discriminatory value4/4, critique4/4, actionability3/4 =19/20 (95%). Subjective confidence is high in these finite exact calculations; confidence in eventual13-smooth exclusion is uncalibrated and is not implied by this score.
