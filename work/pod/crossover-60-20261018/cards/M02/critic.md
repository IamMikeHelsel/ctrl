# M02 independent critique

AI-written independent critic; inherited root model, exact identifier unavailable. Original work/273 files and other-owner jobs preserved. No remote or inference jobs launched.

## Faithful question and source state

The target is every finite family of distinct moduli m≥4, each m+1 prime and every prime factor of m among 2,3,5,7,11, with arbitrary residue choices and unrestricted exponents. It is not the full Erdős 273 problem. The present seven-smooth source reports a completed restricted-family Lean theorem. The eleven-smooth source remains exact Python evidence; no approved Challenge binding or novelty claim follows.

The roster's probe-11.json has only six prefix moduli and 8,280 unresolved nodes. The current successful checker uses eight prefix moduli (4,6,10,12,16,18,30,36), period720, and matches probe-11-symmetric.json. The latest thirteen-smooth source records a 240-second time limit, not a complete exclusion or covering witness. Distinguishing these versions matters.

## Exact independent replay

critic_tree.py imports no producer implementation. It reconstructs all 29,400 exponent tuples, retains 5,265 distinct even moduli passing both Fermat filters, groups exact reciprocal masses by gcd with720, and constructs masks by explicit residue enumeration. It obtains 3,518 distinct states, 3,271 strict prunes, 2,614 memo hits, no open leaves, and minimum density gap

50661803066306609 / 1239915812357376000000 ≈ 0.00004085906685.

The unconditioned upper mass is 728347923255532331431/619957906178688000000 >1. The exact outside-box tail is 1806085527193/7116137582400000. I recomputed that tail by the disjoint first-outside-coordinate partition, rather than the producer's total-minus-box formula. It includes all exponent values beyond the box; it does not test only a finite extension.

Fermat filtering can retain composite pseudoprimes, which weakens the upper bound and is sound. For an admissible m≥4, m+1 is a prime≥5, so bases2 and3 are nonzero modulo that prime and the Fermat identities apply. Treating every retained successor as prime would be wrong, but the capacity calculation does not require that. Distinctness and unique prime factorization prevent repeated reciprocal charges for the same modulus. Four residue classes modulo4 are an immediate counterexample if distinctness is removed: they cover all integers while each successor5 is prime and4 is eleven-smooth.

## Branch coverage, symmetry and memoization

At depth d, translation by the lcm of already assigned prefix moduli fixes every old congruence class and thus the uncovered set. Its orbits modulo the next modulus m have representatives 0 through gcd(lcm,m)−1. Translating the whole remaining assignment preserves capacities and covers all residue choices. The independent replay verifies 7,030 explicit rotation equivalences across all unpruned states and every next-modulus residue, including invariance of the old uncovered set.

The gcd orbit count is essential. With old modulus4 and new modulus6 in period12, assigning residue0 leaves8 uncovered points while residue1 leaves7; these cannot both be normalized to0 by an old-class-preserving translation. The actual eleven-smooth tree also contains identical uncovered bitsets at different depths. Memoization therefore retains both depth and bitset, equivalently the remaining-modulus state; bitset alone does not generally preserve the remaining capacity problem.

Adding any missing prefix modulus with an arbitrary residue can only decrease the uncovered set. These prefix moduli are admissible and distinct. The full argument still must formally bind this augmentation, all arbitrary integer residues, smooth-modulus representation, CRT intersection counts, finite distinctness and the universal exponent tail. The tail result alone does not discharge those bridges.

## Actual consumer mutations

The original check_eleven self-tests reject noncanonical keyword arguments before inspecting a modified proof object. That is useful interface validation but not a certificate corruption test. critic_tree_certificate.json stores the reconstructed graph, and a separate consumer recomputes each state's capacity and exact required children. Removing a branch, falsifying a root prune, altering the claimed uncovered state and understating a leaf capacity all reject through that consumer. Coverage checks permit shared child states but require every canonical branch and correct state/depth binding.

These are exact Python checks, not a Lean-checked full tree certificate. No floating-point comparisons determine the proof decisions. The implementation uses assertions and is intended to run in normal mode; do not treat optimized Python execution as a trusted checker configuration.

## Thirteen-smooth obstruction and limited refinement

critic_thirteen.py independently reconstructs the 22,944-modulus thirteen-smooth pool, its full geometric tail, and the single saved worst prefix assignment. That leaf has1,574 survivors and excess355965731451484909486943/8853308879184753984000000. Splitting on42 gives33 unique child states. For every one, the tested next-modulus menu {40,60} chooses60. The result has891 unique children, only1 pruned, and positive worst excess223417580362732718172257/17706617758369507968000000. The alleged adaptive choice provides no gain over fixed42,60 on this menu.

This positive excess means the sum-of-separate-capacities relaxation is inconclusive. It does not certify a realizable covering, an impossibility of every larger prefix, or an obstruction intrinsic to thirteen-smooth numbers. Pairwise overlap constraints and refined residue partitions are plausible next tests, but must retain all branch choices and account for each modulus exactly once.

## Kernel boundary and gate

All three printed domain_tail.lean lemmas independently compile with permitted axioms. The first natural index a represents the exponent a+1 of2, so range14 means powers1 through14, matching the source. Its final theorem quantifies every finite exponent set disjoint from the box, with no upper exponent bound. The five-prime total is77/32. These are genuine universal-tail results, not a full eleven-smooth covering theorem.

GO for assembling the independently checked eleven-smooth tree into a statement-faithful kernel certificate and full covering-family theorem. HOLD calling that universal exclusion Lean-certified until mass/sieve, orbit coverage, tree recursion and arbitrary-family binding are assembled. GO for a bounded thirteen-smooth coupling test on the declared saved leaf, with complete branch coverage; NO-GO for calling its current excess a covering witness or crediting the tested adaptive menu with an advantage.

Quality 19/20, subjective rather than a probability. No claim of priority, publication or full Erdős-problem resolution.

Final kernel audit: all four domain_symmetry.lean declarations independently compile with permitted axioms. They prove prime-successor Fermat inclusion, existence of a canonical residue by an integer multiple of the prior stabilizer, preservation of prior classes, and equivalence of translated new-class membership. They do not yet assemble the finite capacity graph into the covering-family conclusion.

Further consumed-payload controls reject omitted depth and an underestimated tail. The tail field is compared with the independently derived disjoint geometric sum. The independent reconstruction does not import source checker functions, but its own producer and consumer share its bound helper: corruption tests are not an additional independent derivation of that helper. Exact source-versus-critic agreement, orbit tests and the separate Lean bridges provide distinct evidence.

Disjoint-pair extension independently verified: all fifteen pair gains and all76 partial matchings reproduce. Disjoint pairs (42,60) and (70,72) save13/5040 in density, leaving positive excess333129815691682964686943/8853308879184753984000000. The correction is valid because each of the four moduli is replaced exactly once by a pair-union maximum; remaining moduli and the infinite tail are unchanged. Adding savings from overlapping pairs is generally unsound: three identical singleton coverage sets have separate capacity3 and pair savings1 each, but subtracting all three predicts0 despite union size1. The supported coupling remains insufficient to close this saved leaf.


Further state-quotient audit: same uncovered set at the same fixed-prefix depth is lossless for the original problem, because the consumed and remaining moduli are identical and all future residue choices are independent of the past representation. critic_memo.py checks108 representative future assignments and records the general structural argument. An added rule tying a future residue to a past residue changes this: 4@0 with12@0 or12@4 gives the same uncovered set, but r6=r12 mod6 gives different legal children. Dynamic refinement also needs the actual consumed/remaining modulus set: 4@0 with12@0 or36@0 has identical survivors and depth but different remaining pools.

The generic domain_crt.lean and its720 specialization independently compile with permitted axioms. They import the existing Research.CoveringCRT module and bound an actual class intersection in every common period H by H*g*C/(B*m). They do not assume independence of congruence classes. The original counting source was inspected; no original rebuild was performed. Full assembly still needs survivor-range membership, integer-residue binding and the finite-family/tail combination.

Four- and six-modulus coupling audit: independent exhaustive pair checks give maxima192 for(42,60),97 for(70,72),141 for(40,112). Residues(5,23,14,33) attain289 and residues(5,23,14,33,6,10) attain430. These attain the sums of the pair maxima, so no larger joint gain is possible within either specified block on this leaf. The short upper-plus-attaining-witness proof covers every tuple without trusting the producer's dominance pruning. Lowered maximum, wrong witness and omitted modulus mutations reject.

Weighted relaxation obstruction: critic_weighted.py independently evaluates the saved normalized nonnegative weights against the reconstructed13-smooth pool. The exact upper bound is3935759400011208570822991/3623046402866376245760000, approximately1.08631217; negative weight, wrong normalization, wrong residue and understated objective mutations reject. The infinite tail term is P*tail*max(weight), not just tail after arbitrary normalization.

Stronger than failure of those proposed weights, critic_fractional.py independently consumes the rational fractional certificate. Every group has nonnegative coefficients whose total is at most g*mass_g, the singleton-tail coefficients total at most P*tail, and every one of1574 survivor residues receives at least1.0863121700283507. Multiplying pointwise coverage by arbitrary nonnegative weights summing to1 proves that every weighted single-capacity relaxation of this exact form has objective at least that bound. Budget, cell-omission, wrong-residue, negative-coefficient and exaggerated-minimum mutations all reject. This is exact rational evidence for a route-level NO-GO on this fixed leaf, not an actual congruence covering, not LP solver optimality trusted without a certificate, and not a no-go for larger branches or coupled-capacity models. The implication is presently hand-derived from the checked certificate, not yet an assembled Lean theorem.

Final joint-capacity module: all four domain_joint_capacity.lean lemmas independently compile with permitted axioms after the failed implicit-binder attempts were repaired. They justify chosen-pair coverage, dominance by separate maxima, an unavoidable-overlap discount and a strict joint-plus-remainder budget yielding an uncovered point. Complete candidate families and a valid remainder bound are explicit premises; no actual thirteen-smooth exclusion is asserted.

Final generic duality replay: all three domain_duality.lean declarations independently compile with permitted axioms, including the grouped budget formulation. This proves the finite weak-duality implication used above. The concrete rational multipliers and source-derived budgets remain independently checked Python inputs, not instantiated Lean premises. Total independently replayed printed declarations across tail, symmetry, CRT, joint capacity and weak duality:16. Hashes are recorded in critic_lean_hashes.json; scoped critic Python checks pass.

Additional representation acceptance: all three domain_representation.lean declarations independently compile with permitted axioms, bringing the independently replayed printed total to19. From m≥4, prime(m+1) and an explicit five-prime power-product representation, the module proves a positive exponent of2. A finite set of moduli is represented by a chosen finite tuple set on which modulus is injective; this handles distinctness without assuming global uniqueness of exponent representations. The exact reciprocal identity matches the tail weight. The smoothness premise is explicitly existential power-product form. Equivalence with a literal “all prime factors belong to {2,3,5,7,11}” predicate is mathematically standard but is not proved by this module, so that formal bridge is not claimed as accepted here. No exponents are capped in these representation theorems.
