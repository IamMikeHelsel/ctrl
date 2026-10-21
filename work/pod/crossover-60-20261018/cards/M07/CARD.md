# M07 — Exact dissertation symbol reconstruction

**PM decision: GO for resolving a localized sign discrepancy. The complete signed six-fixture reproduction remains HOLD.** AI-written four-role initial review; elapsed substantive work is in state.json. No earlier inventory entry is counted as a completed proof review.

## Frozen question and source

Can an exact reconstruction of the dissertation Appendix A symbol map reproduce all six supplied ten-coefficient fixtures, including the singular control, for its448-by-448 matrix?

The frozen sources are READ-ME.txt, software/thesis-appendix/README.md and determinant-fixtures.json in `/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/gu-source-exploration-20261018`. Their hashes remain unchanged; see source_binding.json. Raw scan and OCR remain in `/Users/mike/Documents/Codex/2026-10-18/do-more-work-with-a-team/exploration`. The scan hash is11cb75f7edcd7f2371271f672e69d978189a11dd8c94f2cc5df3546b4abcaea7. Root and workers visually checked the relevant source pages rather than executing OCR. The source attributes code to Dror Bar-Natan and algebra to Eric Weinstein.

Previous work reconstructed elementary exterior operations and checked85,348 finite identities. It did not assemble the symbol or compute any supplied determinant. This review constructs a new exact rational candidate; it preserves the original files and their reproduced:false flags.

## Crossovers and assumptions

1. **Compiler translation validation:** independently implement the source operators and compare every matrix entry, while separately binding basis order and scalar pairing. The primary producer uses tuple-based exterior algebra; the critic uses fresh bit-mask signs and double-form operations. They share the declared provisional ordered basis list, an explicit independence limitation.
2. **Coding syndromes and exact certificates:** use modular rank/determinant checks to locate discrepancies, then exact small-block elimination and explicit null witnesses. A modular zero is not a rational singularity certificate; diag(101,1) is the negative control. The source's singular fixture is tested with rational witnesses, not only zero residues.
3. **Unexpected representation and metamorphic route:** sparse support partitions the large matrix into tiny blocks. Coefficient scaling, covector changes, basis rescaling and global sign each preserve different invariants. A448-dimensional determinant cannot detect M→−M; matching determinants alone therefore cannot establish the right operator.

The reconstructed source conventions use dimension8, the source star/wedge/interior operations, full projections, input order L1,L3,Y2,Y4+, target order L4+,Y3,L2,Y1, source coefficient order, covector w1 and the driver's outer scaling m→2m. Signed summands within tracefree bases use provisional lexicographic order; Mathematica2 Plus ordering has not been independently recreated. A fixed basis reorder could multiply all determinants by one common sign, but cannot repair coefficient-dependent sign disagreements.

## Tests and actual results

Domain checks recover projection ranks35,160,350 and the self-dual224-dimensional subspace with exact idempotence and wedge/interior kernel tests on the complete bounded ambient bases. All declared source and target basis dimensions are recovered. No expected determinant values enter operator construction.

Root built all six448×448 rational matrices; after the source outer factor2, all entries are integers. Independent critic bit-mask operators reproduce EVERY entry of all six matrices. Root fraction-free Bareiss and critic rational Gauss-Jordan independently compute exact determinants, accounting for row/column permutation signs.

| Fixture | Exact magnitude vs source | Signed determinant vs source | Reconstructed rank |
| --- | --- | --- | ---: |
| A.1 | matches | matches |448|
| A.2 | matches | matches |448|
| A.3 | matches | opposite sign: reconstructed positive |448|
| A.4 | matches | opposite sign: reconstructed positive |448|
| A.5 | matches | matches |448|
| A.6 | zero matches | zero matches |413|

Thus four of six signed fixtures match, including the singular control; all five nonzero magnitudes match exactly. This is **not complete six-fixture reproduction** and not an established correction of the dissertation. The scan visibly prints negative signs for all five nonzero cases. Ratios[1,1,−1,−1,1] rule out one fixed orientation/normalization repair; coefficient-dependent translation or source-fixture issues remain to localize.

Most matrices split into64 disconnected7×7 bipartite components. A.3 splits further; A.6 includes35 zero input rows and35 rectangular6×7 components. Exact rational elimination establishes rank413. The35 zero rows are precisely L3 basis triples avoiding direction1: the projected forms themselves vanish before pairing, identifying a candidate kernel Λ³(w1-perp). Domain actual-form evaluation and critic independent matrix reconstruction support the claim; explicit rational right-null witness and one-entry mutation are saved separately. No full kernel source-map theorem is claimed.

Independent whole-target Gram analysis gives det(Gtarget)=2^164·3^28. Pairing against target vectors differs from extracting coordinates by this factor. The driver's separate m→2m contributes2^448. Applying it only to fixture A.2 would confuse section A.2 (the driver) with equation(A.2) (the second fixture). The printed c2L4 versus c2L4p assignment discrepancy is preserved; coefficients are supplied explicitly from each fixture, not silently inferred from that typo.

Every entry of all six doubled-coefficient matrices obeys the source row/column degree law. Independent exact determinants scale by2^469, not2^448:56 input rows depend on the injection pair and413 output columns on projection coefficients. There are74 nonzero degree-zero entries in each tested fixture. This is a successful falsifier of naive homogeneous matrix scaling.

For A.1, exact finite covector tests at e2,−e1 and e1+e2 match predicted determinant factors1,1 and2^224. The mixed covector creates blocks up to14×14. These finite checks support consistency; they do not prove covariance for every covector or ellipticity.

## Critique, evidence and continuation

Evidence is exact rational Python arithmetic, two operator implementations with a shared provisional basis list, independent exact determinant algorithms, scan inspection and finite metamorphic tests. No new Lean theorem, independently kernel-checked448-dimensional certificate, novelty result, GU physical validation or ellipticity proof is accepted. Existing frozen Lean challenges remain unchanged. A local SymPy availability probe failed; exact computations use standard-library fractions, not an installed new dependency.

Quality rubric: faithfulness4, reproducibility4, discriminatory value4, independent critique4, actionability3 = **19/20,95%**. Subjective confidence is high in the saved integer matrix arithmetic and the reproducible discrepancy; source faithfulness of every ordering detail remains unresolved. No calibrated probability assigned.

After all60 initial reviews, spend one30-minute block on the exact7×7 block responsible for the A.4/A.5 relative sign, independently reconstruct the source basis order and all coefficient substitutions, and build a source-bound kernel certificate interface with20 semantic mutations. Require resolution or a narrowly stated irreducible discrepancy before marking all signed fixtures reproduced. Retain all failed comparisons, exact witnesses and original source records. No outreach, publication or source correction is authorized.

Artifacts: domain_double.py, domain.md, inventor.md, critic.md; pm_symbol.py and six sparse matrices; pm_exact_det.json; critic_symbol.json; critic_operator.json; inventor_gram.json; inventor_scaling.json; pm_covector.json. Reproduce with uv from this directory's scripts. Primary source: [dissertation Appendix A scan](https://theportal.wiki/images/4/4f/Eric_Dissertation_-_Extension_of_Self-Dual_Yang-Mills_equations_across_the_8th_dimension.pdf).

Final algebraic localization: for the fixed eight output coefficients of A.3–A.5 and injection parameters a=c1L3,b=c2L3, the reconstructed determinant is `2^491*3^43*5^21*7^8*(5a+6b)^21*(5a-3b)^35`. The block partition has8 constant blocks,21 blocks with the plus factor and35 with the minus factor. Each variable block has exactly one parameter-dependent row; the remaining six rows are unchanged. A direct independent source-form calculation gives one seven-block determinant768(5a−3b). Four fresh exact matrix checks include the two singular lines (a,b)=(3,5),(6,−5) and two nonsingular points. This localizes the relative sign issue; it does not justify editing the source or claiming all-six reproduction. See pm_two_parameter.json and domain_sign_block.json.
