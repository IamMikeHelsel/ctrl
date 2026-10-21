# M07 inventor — translation validation before determinant acceptance

AI-written independent inventor role; inherited root model, exact runtime identifier unavailable. PM owns elapsed time and final decision. The first script constructs the448-dimensional TARGET BASIS and its exact Gram blocks. A later initial-session supplement uses PM's candidate symbol assembler and independently checks exact determinants and coefficient scaling. Five absolute determinant values match, but two signs remain inconsistent with the source; full faithful reproduction is not established.

Read frozen CARD, original notebook README/audit, exterior_core.py, six source fixture transcriptions, and raw appendix OCR (never executed). Raw scan located at `/Users/mike/Documents/Codex/2026-10-18/do-more-work-with-a-team/exploration/sources/thesis-1992.pdf`; page71 was rendered to inventor_page71.png and visually inspected against the target basis/assembly definitions. The [primary dissertation scan](https://theportal.wiki/images/4/4f/Eric_Dissertation_-_Extension_of_Self-Dual_Yang-Mills_equations_across_the_8th_dimension.pdf) was also opened. Attribution remains Bar-Natan code and Weinstein algebra. Original files and approved Lean challenges remain unchanged.

## Transfer 1 — compiler translation validation with an explicit observation map

Treat source Mathematica expressions as an intermediate representation. A basis constructor, operator, and observation map each need their own typed validation. In particular, source `sp` evaluates ambient coefficient pairings against constructed basis elements. A coordinate-extraction replacement changes the observation map if that basis is not orthonormal.

Write C with one input basis element per row and output-coordinate coefficients across columns. If G is the target Gram matrix, source pairing assembly is M=C G. Its determinant is therefore det(C)det(G). This identity does not require the source input basis to be orthonormal, provided C uses that same input basis. A transpose convention must be recorded; determinant equality alone will not detect a transpose.

Exact test: inventor_gram.py independently constructs all448 target vectors in sparse ambient wedge/tensor coordinates. It verifies disjoint support between declared blocks, computes every small block determinant rationally, and obtains:

| Target component | Dimension | Gram determinant |
|---|---:|---:|
| self-dual4-forms | 35 | 2^-35 |
| Y3 shift blocks | 210 | 4^70 |
| Y3 raise blocks | 140 | 6^28 |
| 2-forms | 28 | 1 |
| Y1 off-diagonal symmetric tensors | 28 | 2^28 |
| Y1 trace-free diagonal tensors | 7 | 8 |

Total **det(G)=2^164·3^28**. Each `kertr[d]` block is the Gram matrix of successive differences of d signed orthonormal terms, with determinant d. Shift terms have the left tensor index absent from the right blade; raise terms contain it. These classes are disjoint; within either class the underlying union or residual pair labels separate blocks. Self-dual basis elements have squared norm1/2, not1.

Combined with the source driver's independent outer doubling of a448×448 matrix, the printed-pairing versus coordinate-determinant factor would be **2^612·3^28**. This is a conditional normalization conversion, not a determinant computation or confirmation of a printed fixture. Root independently derived the same factor; critic replay requested.

Preserves: exact source spaces, rational normalization, and distinction between coordinates and pairings. Falsifier: treating the target Gram as identity predicts an incorrect factor. Limits: Gram determinants do not determine exact term order or basis orientation, do not validate the projections, and do not establish faithful final assembly. Mathematica term-order changes within each orthogonal-term block cannot affect these Gram determinants, but source row/column ordering remains a separate obligation.

## Transfer 2 — coding syndromes for debugging, with adversarial collisions

Map each supplied factorization to a short modular fingerprint. This can reject a reconstruction or distinguish modeled transcription mistakes cheaply before an expensive exact determinant. It is a debugging code, not a replacement for proof.

Exact source-only fingerprint modulo97, in fixture order A.1–A.6, is `(35,87,84,29,90,0)`. Moduli2,3,5,7 produce zero for ALL six reported determinants, so they do not distinguish the five nonsingular source fixtures from the singular control. Mod11 also makes A.3 zero and mod29 makes A.2 zero. A modular zero therefore does not imply rational singularity. A nonzero modular determinant of a properly denominator-cleared integer matrix would certify nonsingularity. These initial fingerprints themselves do not use a reconstructed matrix; the later supplement below does.

Concrete error-localization test: compare observed/expected determinant ratios at primes(97,101,103). An odd one-sided permutation gives `(96,100,102)`; omitting the target Gram factor gives `(96,16,68)`; omitting the source matrix doubling gives `(35,97,91)`. Thus a single mod97 fingerprint confuses a Gram omission with a sign error; adding101 separates this finite list. This does not classify every possible bug.

Unexpected collision control: integers1 and1009092 have identical residues modulo97,101,103 but are unequal. Matching finitely many primes cannot establish exact determinant equality without a justified size bound and CRT reconstruction or another exact certificate. Likewise, singular A.6 needs an exact null vector or exact elimination certificate once the matrix is built, not repeated modular zeros. Preserve the actual integer/rational matrix, denominator-clearing rule, pivots, and source-basis binding.

## Transfer 3 — metamorphic representation tests, including a non-obvious degree

Change the representation while preserving the underlying map, then predict what must change in the matrix. This tests normalization without needing an oracle for the final determinant.

Exact three-dimensional block test: an A3 Gram matrix has determinant4. Double one target basis vector. The new Gram determinant is16, but the same map's pairing matrix determinant is8 because its coordinate matrix changes reciprocally. A naive “Gram scales twice, therefore the pairing determinant scales twice” rule is false. In general, target change W→W D sends G→DᵀGD, row-coordinate matrix C→C D^-T, and pairing M→M D. Independent input change V→V U gives M→Uᵀ M D. Two compensating permutations can leave a determinant unchanged while the indexed matrices differ, so acceptance also needs entry/basis fingerprints.

A second source-derived metamorphic contract is more surprising: scaling ALL ten coefficients by lambda is not scaling the entire matrix by lambda. The L3 injection pair scales56 input rows; projection groups scale35+350+28=413 output columns, while the Y1 projection is coefficient-free. Conditional on the literal source dependency structure, `det M(lambda c)=lambda^469 det M(c)`, whereas directly doubling M gives2^448. Groupwise degrees are56,35,350,28. Setting a complete projection group to zero must create its corresponding zero-column block; setting the injection pair to zero gives56 zero rows. The all-ones singular fixture is not such a trivial zero-group control.

Domain role independently reports actual pre-doubling entry checks in domain_homogeneity.py/json: one L3→L2 entry is−7/2,−14,−63/2 at lambda1,2,3, while an L1→Y1 entry remains−6. These corroborate quadratic versus constant entry behavior; this inventor note attributes that test rather than claiming an independent replay. The initial Gram script stores the predicted full homogeneity contract. The later supplement tests it against the assembled candidate.

Preserves: the linear map under basis changes, and typed coefficient dependencies under parameter scaling. Falsifiers: forget reciprocal coordinate rescaling; confuse parameter scaling with outer matrix scaling; silently permute one coefficient group; or accept unchanged determinants as proof of unchanged indexed operators. Limits: successful metamorphic tests do not establish agreement with the source, because a consistently wrong implementation can satisfy the same invariances.

## Evidence and decision proposal

`uv run python work/pod/crossover-60-20261018/cards/M07/inventor_gram.py` produces inventor_gram.json/log. All arithmetic is Fraction/integer; no optimizer or downloaded code is executed. Scoped Ruff lint/format checks pass. Exact target Gram reconstruction is new executable evidence; source fixture residues remain computations on transcriptions. No Lean certificate, novelty claim, ellipticity proof, or physical interpretation is established.

Later initial-session supplement: inventor_scaling.py calls PM's candidate assembler for ALL six coefficient vectors doubled by2. It verifies every one of448² entries against the expected source-row and target-column factors, then independently computes exact original/scaled determinants by rational Gaussian elimination on bipartite components. All six entry checks pass. All five nonzero determinants scale by2^469 and reject the naive2^448 law; A.6 remains zero. There are74 nonzero degree-zero entries in every candidate fixture. This is independent validation of a shared assembler, not an independently transcribed implementation.

That independent exact determinant calculation confirms PM/critic findings: source ratios for A.1–A.5 are `(1,1,−1,−1,1)` and A.6 is zero. Therefore A.1/A.2/A.5 signed values match; A.3/A.4 match absolute values but have positive rather than printed negative determinants. A single fixed invertible source/target basis change or constant normalization multiplies all determinants by the same factor. It cannot fix just those two signs while preserving the other three. Coefficient-dependent changes, source transcription/printing, or an operator implementation discrepancy remain possibilities; no preferred repair is justified here. Critic's rank413 for A.6 is separately attributed; this inventor determinant test does not independently certify that rank.

Recommendation: GO for a source-bound assembly acceptance test and targeted sign-discrepancy investigation. Next action: emit a separately formed coordinate matrix and verify `M=C G`, then audit source coefficient assignments and all operator signs against scans. Include deliberately missing1/2, omitted outer2, basis permutation, coefficient-name mismatch, and singular-control mutations. HOLD full fixture reproduction until the two signed discrepancies are resolved with evidence; do not patch fixture-specific signs. Even all six determinants would not alone establish symbol covariance or invertibility at all nonzero covectors.

Quality: faithfulness4, reproducibility4, discrimination4, critique4, actionability3 =19/20 (95%). Subjective confidence high in the target Gram arithmetic and explicit negative controls; this is not a calibrated probability of successful full reconstruction.
