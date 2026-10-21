# M07 domain record: exact Appendix A reconstruction

AI-assisted domain researcher; inherited model, exact model ID unavailable. This is isolated campaign research, with no original source or approved challenge edits. Root owns substantive-session timestamps and the PM decision.

The frozen question is whether the ten-coefficient Appendix A symbol construction reproduces all six supplied 448×448 determinant fixtures, including the singular control. The source is the 1992 thesis Appendix A, attributed there to Dror Bar-Natan (Mathematica) and Eric Weinstein (algebra). This does not establish a later GU equation, physical model, or novel mathematical result.

## Source binding and recovered conventions

Original PDF: `/Users/mike/Documents/Codex/2026-10-18/do-more-work-with-a-team/exploration/sources/thesis-1992.pdf`, SHA256 `11cb75f7edcd7f2371271f672e69d978189a11dd8c94f2cc5df3546b4abcaea7`. Original source OCR remains a search aid, not executable authority. I visually inspected the projection/basis scans, including the rendered page71 retained as `domain_source_page71.png`. The primary source is https://theportal.wiki/images/4/4f/Eric_Dissertation_-_Extension_of_Self-Dual_Yang-Mills_equations_across_the_8th_dimension.pdf .

The exact elementary implementation imported read-only is `/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/gu-source-exploration-20261018/software/thesis-appendix/exterior_core.py`. `domain_double.py` adds sparse Fraction doubleforms and source-defined raise, shift, lower, exchange, wedge/interior contraction, and Y projections. It contains no expected determinant values.

The source uses Euclidean dimension8, its printed Hodge/interior convention, self-dual projection with factor1/2, and finally doubles the entire scalar-pairing matrix. Domain input dimensions are 8+56+160+224; target dimensions are35+350+28+35. The scalar pairing `sp` is an ambient coefficient pairing, not target-basis coordinate extraction. Source driver spelling `c2L4` versus `c2L4p` remains a disclosed ambiguity; no source text was repaired.

Within each signed-summand basis recipe, our term order is lexicographic. Exact Mathematica Plus ordering is not yet independently reconstructed. Different fixed orders change orientation by a coefficient-independent sign; this cannot repair the mixed fixture sign discrepancy below.

## Exact positive tests

`domain_projection.py` checks 1016 ambient cases: projection idempotence, vanishing wedge/interior traces, and self-duality where required. Every constructed Y basis vector is fixed. Exact trace/rank totals agree with35,160,350,224. Cross-block Gram entries are zero and small rational Gram determinants give:

- L4+: 2^-35.
- Y1: 2^31.
- Y2: 3^56·7^8.
- Y3: 2^168·3^28.
- Y4+: 2^224·5^56.

Thus the full target Gram determinant is2^164·3^28. Using coordinates instead of the printed scalar pairing changes the determinant by this factor; the first L4+ basis vector has norm squared1/2, a concrete negative control. Critic and inventor independently recovered this normalization.

The root used the API to construct all six full matrices. Root exact fraction-free determinants match all five NONZERO ABSOLUTE fixture values, and the sixth is zero. A1,A2,A5 signed values match; A3,A4 have opposite signs. The critic independently reconstructed all six matrices with a bitmask exterior operator implementation and matched every entry, while sharing the basis vectors. This is a substantial reproduction with a material unresolved signed-source discrepancy, not acceptance of all six signed fixtures.

## Sign-crossing discriminator

`domain_sign_block.py` independently implements the required source projections for one representative block, without importing the PM map or determinant routine. The doubled L3 input w234 to target cleavep(w1234) entry is

`a*(-4*c1L4p+c3L4p) + 3*b*c2L4p`,

where a=c1L3 and b=c2L3. For A3–A5, this becomes `-5*a+3*b`. The complementary six-dimensional Y2/Y4+ to Y3 minor has determinant−768, computed directly by the permutation definition. The whole seven-dimensional block is therefore `768*(5*a-3*b)`, giving1536,3840,−2304 at A3,A4,A5. Root's graph decomposition finds35 copies with fixed orientation signs. Their odd multiplicity makes the A4/A5 sign change intrinsic to this reconstructed operator. A fixed row/column reordering cannot remove it. This narrows the unresolved issue to source fixtures, coefficient-dependent source semantics, or a still-undetected mapping discrepancy; it does not assert the thesis is erroneous.

## Singular control and scaling traps

`domain_kernel.py` checks actual projected forms, not only matrix pairings: at A6 all35 L3 triples avoiding the covector direction w1 have all four outputs exactly zero. This identifies the subspace Λ³(w1-perp). Together with root's modular rank413 certificate, the rational kernel dimension is exactly35 and this subspace spans it. This script explicitly imports the PM symbol assembly; independent operator support comes from the critic, not from treating this import as independent.

`domain_homogeneity.py` independently checks two source entries. Scaling all ten coefficients by λ multiplies L3-to-L2 entry−7/2 by λ², while L1-to-Y1 entry−6 is unchanged. Hence scaling coefficients is not uniform matrix scaling. The inventor's structural determinant degree469 is consistent with56 scaled input rows plus413 scaled output columns; these two entries provide a concrete falsification of the naive degree448 assumption, not a complete determinant homogeneity proof by themselves.

## Evidence and next action

Evidence level: exact rational executable checks and independently reconstructed finite matrices; no Lean theorem or accepted challenge result for this reconstruction. No novelty claim. Source signed fixtures remain unreproduced at A3,A4. Recommended decision: GO for the source-binding investigation; HOLD acceptance of “all six signed determinants reproduced.” Precise next action: audit the printed fixture signs and Mathematica evaluation/ordering semantics against the reconstructed coefficient-polynomial block factors, then serialize small-block determinant certificates for independent kernel checking once the intended matrix is fixed.

Quality grade for this bounded domain contribution:4/5 (source-bound exact implementation, negative controls, independent crosschecks; signed fixture mismatch and no kernel certificate). Subjective confidence:95% that the current implementation's normalization and finite arithmetic are correct, separately from confidence in complete source interpretation.

Reproduction commands from ctrl root:

```
uv run --no-project --python /usr/local/bin/python3 python work/pod/crossover-60-20261018/cards/M07/domain_projection.py
uv run --no-project --python /usr/local/bin/python3 python work/pod/crossover-60-20261018/cards/M07/domain_homogeneity.py
uv run --no-project --python /usr/local/bin/python3 python work/pod/crossover-60-20261018/cards/M07/domain_sign_block.py
uv run --no-project --python /usr/local/bin/python3 python work/pod/crossover-60-20261018/cards/M07/domain_kernel.py
uv run ruff check work/pod/crossover-60-20261018/cards/M07/domain_*.py
uv run ruff format --check work/pod/crossover-60-20261018/cards/M07/domain_*.py
```

No installed dependencies, original model changes, CLI changes, full repository check, or formal-result acceptance is implied by these isolated checks.
