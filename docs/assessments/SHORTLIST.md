# JSP shortlist — Solved / Lean proof: No (screened 2026-10-17)

Input: `jsp_solved_no_lean_2026-10-17.json` (294 entries). Entries whose formal-conjectures (FC)
statement already carries `formal_proof using lean4 at`, or whose FC file already contains a
sorry-free proof, were excluded. JSP ids are not Erdős numbers; the Erdős mapping was done
semantically and is given in the "area" column as `E<n>`.

FC paths are relative to `/Users/mike/lean-work/formal-conjectures/`.

## Ranked shortlist

| # | JSP id | Title (short) | Area | FC file | Why tractable | Main risk |
|---|---|---|---|---|---|---|
| 1 | JSP-000690 | 3-uniform 3-critical hypergraph, min degree ≥ 7 (E834) | Hypergraphs | `FormalConjectures/ErdosProblems/834.lean` (`erdos_834.parts.ii`, also `parts.i`) | parts.ii is an explicit 9-vertex witness (Li 2025); all FC predicates are Finset/`Fin k` defs, so `decide` over 3^9 colorings closes it; parts.i follows from Bollobás' τ-critical edge bound (≤ C(5,3)=10 edges ⇒ ≤ 4 vertices ⇒ τ ≤ 2) | Kernel `decide` cost (need `Decidable` instances / `decide +kernel`); parts.i needs a Bollobás set-pairs proof, which Mathlib lacks |
| 2 | JSP-000733 | Subset sums never dividing each other (E882) | Additive NT | none | Upper bound is pigeonhole on 2^|A| subset sums; lower bound is the explicit set {2^m − 2^i} (checked by brute force up to m=14) | Statement must be written from scratch; the exact asymptotic form (log₂ n + O(1)) needs care |
| 3 | JSP-000264 | Signed reciprocal set has zero-sum subset (E318) | Additive NT | `FormalConjectures/ErdosProblems/318.lean` (`parts.i`, `variants.contain_single_even`) | Elementary 2-adic valuation argument; FC docstring already sketches parts.i via `contain_single_even` | `parts.ii` (squares, Larsen 2026) is much harder; the bounty claim may need the full problem |
| 4 | JSP-001021 | Every 14-vertex tournament contains TT5 (E1216) | Tournaments | none | Reid–Parker: short case analysis around the uniqueness of the quadratic-residue tournament QR7; finite | Mathlib has no tournaments; brute force over 2^91 is infeasible, so it needs a real argument or a clever SAT certificate |
| 5 | JSP-000288 | Ratios in minimal stably complete sequences (E346) | Additive combinatorics | `FormalConjectures/ErdosProblems/346.lean` (`erdos_346`) | Disproved by an explicit sequence (GPT Pro) whose ratios stay ≥ 6/5 and tend to φ and φ+1/4; parts of Graham's sequence infrastructure are already proved in FC | Completeness of the counterexample sequence is an infinite-family argument; `f_isAddStronglyCompleteNatSeq` is still sorry |
| 6 | JSP-001007 | Avoid half the residues mod many primes (E1202) | Sieve / NT | Related: `FormalConjectures/GreensOpenProblems/44.lean` (labelled open); no ErdosProblems file | Negative answer (Price + GPT) uses intervals plus one long AP; Mathlib has Chebyshev bounds and Bertrand's postulate | Needs explicit prime counts in [m, 2m]; Green 44 is labelled open, so it may not be the same statement |
| 7 | JSP-000490 | Colouring countable sets with finite pairwise intersections (E603) | Infinite combinatorics | `FormalConjectures/ErdosProblems/603.lean` (`erdos_603`) | Short proof once the Erdős–Rado theorem is available | Erdős–Rado is not in Mathlib (cardinal partition calculus) |
| 8 | JSP-000731 | Gaps in the distinct-element sumset of a basis (E880) | Additive bases | none | HHP07: k=2 is trivial; k≥3 uses an explicit construction | Need to write the statement; the construction proof is a few pages |
| 9 | JSP-000307 | Three consecutive integers with decreasing largest prime factors (E372) | Analytic NT | `FormalConjectures/ErdosProblems/372.lean` (`erdos_372`) | Balog 2001 proof is 5 pages; FC statement is clean (`maxPrimeFac`) | Analytic counting (≫ √x such n) may need smooth-number estimates absent from Mathlib |
| 10 | JSP-000078 | Odd cycle lengths vs chromatic number (E58) | Graph theory | `FormalConjectures/ErdosProblems/58.lean` (`erdos_58`) | Gyárfás' proof is a DFS-tree / block argument; Mathlib has `SimpleGraph` colourings and walks | Equality-case characterization is long; cycle-length bookkeeping in Mathlib is painful |
| 11 | JSP-000440 | Ramsey number of 1:2 trees (E549) | Ramsey | `FormalConjectures/ErdosProblems/549.lean` (`erdos_549`) | Disproof (Norin–Sun–Zhao) via double stars with an explicit colouring | Lower-bound colouring is explicit, but the double-star Ramsey count is fiddly |
| 12 | JSP-001010 | Residue-class covering multiplicity (E1205) | Covering systems | none | F→∞ is called a "simple exercise" | F(x) ~ log x needs Chernoff-type bounds; statement written from scratch |
| 13 | JSP-000817 | 2-colouring with short monochromatic APs (E984) | Ramsey / APs | none | Resolved by a short comment (Zach Hunter); likely a random or greedy colouring | Probabilistic step; quantitative growth function needs care |
| 14 | JSP-001003 | Mixed sum-product sets in 2-colourings (E1198) | Ramsey NT | none | Smith 1995 counterexample colouring | Difficulty of verifying the colouring is unclear; source is hard to get |
| 15 | JSP-000751 | Gaps in block counts of PBDs near projective planes (E903) | Design theory | `FormalConjectures/ErdosProblems/903.lean` (`erdos_903`) | EFSW 1985: t > n ⇒ t ≥ n+p, via counting | Counting is intricate; Mathlib has no design-theory API |
| 16 | JSP-000688 | Edges needed for a given hypergraph chromatic number (E832) | Hypergraphs | `FormalConjectures/ErdosProblems/832.lean` | Alon 1985 uses a Turán-type construction; FC hypergraph API exists | Asymptotic bounds; medium-hard |
| 17 | JSP-000760 | Cycle plus a vertex adjacent to three of its vertices (E916) | Extremal graphs | none | Thomassen 1974, combinatorial | Long case analysis; statement written from scratch |
| 18 | JSP-000672 | Critical graphs contain every … (E815) | Graph theory | none | Disproof by Narins–Pokrovskiy–Szabó, with an explicit construction | Criticality is hard to verify formally |
| 19 | JSP-000513 | List multicolourability persistence (E632) | Graph colouring | none | Dvořák–Hu–Sereni give an explicit counterexample graph | List multicolouring must be defined; checking may need a large computation |
| 20 | JSP-000603 | Positive weights on lines through a planar point set (E735) | Discrete geometry | none | ABKPR08 combinatorial argument | Hard; incidence geometry is thin in Mathlib |

## Notable rejects

| JSP id | Reason |
|---|---|
| JSP-000385 | Prime-sum permutation (E473); FC already has `formal_proof` |
| JSP-000598 | E730; FC main statement has `formal_proof` |
| JSP-000301 | E365; `erdos_365.parts.i` is already proved in-file in FC |
| JSP-000087 | E69; already proved in FC |
| JSP-000388 | E477; main statement has `formal_proof` |
| JSP-001018 | E1213; FC has `formal_proof` |
| JSP-000945 | E1140; needs class-number theory |
| JSP-000838 | E1006; needs Nešetřil–Rödl high-girth constructions |
| JSP-000622 | E758; z(12)=4 needs a SAT-scale computation |
| JSP-000198 | Empty hexagon (E216); an existing Lean SAT verification already covers it, and Horton sets are needed as well |
| JSP-000194 | E210; needs Green–Tao |
| JSP-000007, -000035, -000036 | Famous deep theorems, out of scope for days |
| JSP-000884 | E1064; only `variants.k2` is proved, and the main density statement is analytic |

Also excluded because FC already has `formal_proof`: roughly 45 more entries (e.g. 788, 984, 870,
1019, 391, 428, 183, 641, 346, 704, 399, 377/378, 360, 839, 673, 259, 139, 104, 837, 243, 698, 720,
745, 746, 878, 954, 985, 992, 090, 765, 766, 658, 661, 588, 575, 562, 547, 539, 475, 471, 437, 359,
357, 334, 640, 906).
