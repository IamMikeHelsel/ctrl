# Geometric Unity source inventory

Retrieved 2026-10-18. This is a bounded research corpus, not a complete bibliography of Weinstein's public output. Exact download URLs, UTC times, byte counts, and SHA-256 hashes are in `provenance.json`. Raw downloads and extracted transcripts remain local research material; they are not licensed for redistribution by this inventory.

## Acquired material

| File | Work / version | Authority and examination |
|---|---|---|
| `official-home.html` | [Geometric Unity homepage](https://geometricunity.org/) | Author project site. Still presents April 1, 2021 as the latest draft. No newer manuscript established by this search. |
| `gu-2021.pdf` | [Author's Working Draft v1.0](https://geometricunity.nyc3.digitaloceanspaces.com/Geometric_Unity-Draft-April-1st-2021.pdf), April 1, 2021; 69 PDF pages | Primary manuscript. Byte-identical to prior working copy: SHA-256 `3f28d742234a9841fc8e51ff172053200aa3eddf3ece38154a3328b9ebd186d4`. Existing source-to-theorem audit remains applicable. |
| `oxford-official.html` | [2013 Oxford lecture](https://geometricunity.org/2013-oxford-lecture/), released with 2020 commentary | Author project hosts transcript; spoken statements are primary, transcription is an editorial layer. |
| `oxford-2020-supplement.html` | [First Look / supplementary presentation](https://theportal.group/a-portal-special-presentation-geometric-unity-a-first-look/), released April 2, 2020 | Community transcript of the author, including the 2013 lecture and 2020 PowerPoint explanation. Video ID `Z7rd04KzLcg`; not a second independent manuscript. |
| `keating-2021.html` | [Geometric Unity Revealed](https://theportal.group/into-the-impossible-eric-weinstein-geometric-unity-revealed/), 2021 | Community transcript of author interview, including animations. Video ID `uFirZANoiHI`. Useful explanatory context, not a normalized operator specification. |
| `ucsd-2025.html` | [From Dark to Geometric Energy](https://theportal.group/from-dark-to-geometric-energy-a-sector-of-geometric-unity/), April 2025 lecture, page May 22, 2025 | Community page with abstract and only a short introductory transcript. Video ID `fBozSSLxFvI`. Full lecture/slides NOT acquired or frame-verified. |
| `jaimungal-2025.html` | [40 Years in the Making](https://theportal.group/curt-jaimungal-with-eric-weinstein-geometric-unity-40-years-in-the-making/), June 2, 2025 | Full community transcript downloaded. Video ID `ILlhFKuu3NQ`, also titled *Unifying All Forces + Generations*. These are the same interview, not separate releases. |
| `thesis-1992.pdf` | [Extension of Self-Dual Yang-Mills Equations Across the Eighth Dimension](https://theportal.wiki/images/4/4f/Eric_Dissertation_-_Extension_of_Self-Dual_Yang-Mills_equations_across_the_8th_dimension.pdf), September 1992; 76 PDF pages | Primary author dissertation in community mirror. Title, Harvard acceptance certificate, contents and appendix inspected. Extracted text is OCR and can corrupt mathematics. |

All HTML has a plain-text derivative and extracted link list. Both PDFs have page-marked text derivatives. `download.py` reproduces downloads; future retrievals may differ. `derived-manifest.json` records the exact derivatives used here.

## Material that changes the exploration priorities

**The dissertation contains author-associated computational work, with code credited to Dror Bar-Natan.** Appendix A.1 (printed p60, PDF p66 onward) gives Mathematica code for a symbol matrix; A.2 gives example input and A.3 determinant examples (printed p67 onward). The dissertation explicitly credits Bar-Natan for the code and Weinstein for the algebra (printed p5 / PDF p11). This is a concrete computational antecedent worth reconstructing with transcription checks. It is not a released GU software package. The dissertation also has sections on even-dimensional extension, low-dimensional torsion/curvature, elliptic symbol sequences and Spin(10) phenomenology. Its Riemannian eight-dimensional setup must not silently become our split fourteen-dimensional assumptions.

The June 2025 interview has several precise follow-up targets:

- 02:17–02:21: gauge-rotated Levi-Civita contortion, tilted subgroups, and a double-coset account of connection gauge orbits.
- 02:27–02:30: Clifford contraction, its kernel and complement are distinguished while explaining generation labels.
- 02:36–02:41: curvature obstructs the ordinary covariant de Rham differential from squaring to zero; a shortened 0→1→13→14 sequence is discussed as a rolled-up operator.
- 02:42–02:43: a separate two-connection complex is described as unreleased. The transcript is not enough to reconstruct it faithfully.

These are source statements and mathematical targets, not established physical conclusions. The transcript contains visible phonetic errors in technical terms; formulas require checking against video frames and the manuscript. In particular, do not ask for a universally square-zero ordinary covariant de Rham complex as if the author had claimed one.

## Limits and next acquisition

1. Obtain and inspect the 2025 UCSD blackboard/slides and exact formula frames. Its acquired web transcript is incomplete.
2. Reconstruct the thesis code carefully and test its documented determinant examples; preserve every transcription correction against a page image.
3. Resolve differences among manuscript, 2020 supplement and 2025 speech in an explicit convention ledger. Later speech is not automatically a corrected manuscript.
4. No standalone downloadable `.ppt`, `.pptx`, `.zip`, or GitHub software link was found in the acquired source link lists. This is a scoped observation, not evidence that further author-associated software does not exist.
5. Other search results included community formalizations, speculative completions, criticism, and a purported 2026 coauthored SSRN item. None establishes Weinstein authorship or endorsement merely by mentioning/listing his name; they were not promoted into this primary corpus.
6. No account signup, correspondence, payment, private material, or bulk video download was used. Third-party critique and community code are separate investigations.

## Immediate connection to our existing proof library

The most promising next bridge is a source-specified covariance/contraction calculation, with conventions explicit, followed by the symbol/ellipticity antecedent. The existing Clifford normalization family should be tested inside those operations before treating coordinate-distinct maps as distinct GU operators. The previously checked adjoint/signature sector remains a prerequisite, not an answer to these operator questions.

## Independent thesis identity check

The [Harvard Mathematics historical Bott student table](https://legacy-www.math.harvard.edu/history/bott/bottbio/node6.html) independently lists Eric Weinstein, 1992, and the matching dissertation title. Its HTML is archived as `harvard-thesis-identity.html` with provenance. The scan itself dates its title page September 1992 and acceptance certificate September 24, 1992. This establishes bibliographic identity, not completeness or textual fidelity of the community scan. A secondary Google Books record reports a different page count; our 76 refers only to the acquired PDF, not an assertion about every archival copy.
