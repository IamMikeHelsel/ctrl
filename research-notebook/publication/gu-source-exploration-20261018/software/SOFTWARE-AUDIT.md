# Software audit, 18 October 2026

## Most useful discovery: author-associated Mathematica in the 1992 dissertation

The 1992 dissertation contains actual printed Mathematica 2.0 code, Appendix A.1, printed pages 60–66 / PDF pages 66–72. Appendix A.2 provides a driver and A.3 six determinant fixtures, printed pages 67–68 / PDF 73–74. Attribution is unusually precise: thesis printed page 5 / PDF11 says the program was written by Bar-Natan and Weinstein, **the code by Dror Bar-Natan and the algebra by Eric Weinstein**. This is author-associated source code, not solely Weinstein's implementation and not a contemporary GU simulator.

Primary work, community-hosted scan: https://theportal.wiki/images/4/4f/Eric_Dissertation_-_Extension_of_Self-Dual_Yang-Mills_equations_across_the_8th_dimension.pdf . Download: `../sources/thesis-1992.pdf`; SHA256 `11cb75f7edcd7f2371271f672e69d978189a11dd8c94f2cc5df3546b4abcaea7`. Full provenance in `../sources/provenance.json`.

The appendix defines signed wedge normalization, tensor products, Hodge star, interior product, self-dual/anti-self-dual splitting, raise/shift/lower maps, projections, bases and a projected symbol matrix. Its supplied dimensions sum to **448 on each side**: source 8+56+160+224, target 35+350+28+35. Five reported coefficient choices have nonzero determinant; the sixth is zero. The fifth has an indicated geometric inclusion interpretation. These are useful finite targets with a genuine negative control, closer to an author-defined calculation than current community GU reconstructions.

### Work performed here

`thesis-appendix/exterior_core.py` is a new, independent, standard-library Python implementation using rational arithmetic. It reconstructs only the elementary operations on printed page61/PDF67, with explicit oriented Euclidean dimension-eight convention. It does **not** execute the OCR or third-party code. `test_exterior_core.py` passes 85,348 exact checks: all 256 basis blades, star-square and volume pairing, vector contraction against the source star/wedge definition, Clifford anticommutator for the unprojected dee+delta symbol, graded wedge commutation, and the 35-dimensional self-dual basis pivot structure. An explicitly labeled signature extension is tested separately; it is not attributed to the thesis.

The exact check result is `thesis-appendix/core-check-result.json`. This is finite Python evidence, **not Lean proofs**, and not a recovery of the final projected 448×448 symbol. `determinant-fixtures.json` contains visually checked six coefficient tuples and determinant factorizations from PDF73–74. Every fixture is marked `reproduced:false`.

### Specific transcription hazards and next acceptance

- OCR confuses `w`/`v`, `1`/`l`, assignment syntax, indices, exponents and tensor-product infix syntax. Never execute `appendix-OCR-NOT-EXECUTABLE.txt`.
- A.2 scales `m` to `2*m` before the determinant. Reproduction must retain this normalization, source ordering, and basis scaling.
- Printed `sp` is a Kronecker coefficient pairing evaluated against constructed basis expressions; it must not silently be replaced with coordinate extraction in a nonorthonormal basis. Gram factors can change determinant normalization.
- The A.2 assignment line appears to set `c2L4=1` while its print list and A.1 use `c2L4p`. Verify and record any repair rather than silently correcting the source.
- The printed convention for interior product is `star(x wedge star(y))`; parity depends on dimension and degree. Our dimension-eight vector tests establish the corresponding usual vector contraction for this bounded setting.
- Next: transcribe raise/shift/lower, injection/projection and basis definitions against scans; independently derive their source/target spaces; build the 448×448 exact matrix; recover all six determinant fixtures including the singular case; then test symbol covariance and nonzero covectors before claiming ellipticity. Merely reproducing one numeric determinant is not an ellipticity proof.

## Community repositories: source snapshots, not author implementations

All following downloads are pinned and byte-verified against Git blob hashes. `DOWNLOAD-MANIFEST.json` gives exact raw URL, full commit, blob SHA1 and SHA256 for every saved file. We downloaded 175 selected files totaling 1,745,555 bytes. Large repositories are **partial inspections**, not full mirrors. No downloaded repository code, install script, tests, workflow, or agent instructions were executed.

| Repository | Pinned commit | Actual content inspected | Assessment and license |
|---|---|---|---|
| [disruptionjoe/gu-formalization](https://github.com/disruptionjoe/gu-formalization) | `97a491774bd4a345e092f30dd68f6e482f35ae6f` | README, build metadata, all Lean sources, license files | Independent AI-directed reconstruction. Code MIT, documentation CC BY4.0. Useful comparison of proof scope; not evidence of GU validity. |
| [Dizzident/GeometricUnity](https://github.com/Dizzident/GeometricUnity) | `b64af60e7aca3d2eb0f32afb850c3870f06b0e81` | README, selected Clifford/Shiab C# source and tests | Actual numerical platform, not Weinstein software. No license identified in repository API/root listing; no open-source reuse permission inferred. Partial static inspection only. |
| [justindbilyeu/geometric-unity-gate1](https://github.com/justindbilyeu/geometric-unity-gate1) | `2fcaf716ccd3323c39f8901862a58385507b6662` | All 24 files | MIT. Markdown claims and AI exchanges, **no executable proof or symbolic calculation files** in tree. A uniqueness claim requiring independent checking. |
| [disruptionjoe/gu-source-action](https://github.com/disruptionjoe/gu-source-action) | `cf6b5c8c11e3fa2ffa8eae5e3d11be5a19bc33b0` | Source/docs except agent directives | Independent Python sandbox. README explicitly says no source action constructed. Imports sibling Cl(9,5) machinery; not drop-in Cl(7,7) evidence. No license identified. |
| [disruptionjoe/dynamic-unity](https://github.com/disruptionjoe/dynamic-unity) | `af4b9d5cdec2fa398b1b8cc26f14d1f1b02b3c2d` | README and tree metadata | Independent extension research; not author source. No license identified. Low immediate priority. |
| [yutk/gu](https://github.com/yutk/gu) | `600689498c63b93ca49aa5e215356d3d0118030b` | All 10 files | Text excerpts of GU mathematical prose, not software. No license identified. |
| [stubbornjello-oss/gu](https://github.com/stubbornjello-oss/gu) | `7083c3f9c048a631abaa29642ead4ca5cfcdc538` | All 9 files | Text excerpts, not software. No license identified. |
| [ResponseGU/Response_to_Geometric_Unity](https://github.com/ResponseGU/Response_to_Geometric_Unity) | `6cba966b66d99329eabd26b2a1b776bb7f4a3810` | Complete tree: one PDF | Criticism document, no software in tree. No license identified. |

### Three concrete scope findings

1. **Finite certificate versus representation theory.** `disruptionjoe`'s `Lean/GUFormalization/ShiabMultiplicityCertificate.lean` defines six irreducible labels and hard-coded multiplicity tables. Lean proves finite arithmetic (dimensions and overlaps), including a full-Dirac table sum of four and chirality-flipping sum of two. The file explicitly says it does not construct the decompositions, prove the D7 theory, select GU's Shiab, or identify a physical real form. We have not built their Lean library. Do not transplant its numerical count into a differently typed Hom space.
2. **A reduced numerical model deliberately drops source structure.** `Dizzident`'s `EinsteinianShiabOperator.cs` documents a Euclidean Cl(4,0), four-dimensional Lambda2 slice, output degree2, and omission of the literal degree-raising Hodge/wedge legs. It also accepts `i-anticommutator` as a recorded parameter without changing real-valued numerics. Its family coefficient defaults to 0.5 by Einstein analogy. Those are explicit, material modeling boundaries. Its tests could validate that reduced model without validating the source operator. The README's large test counts were not independently rerun.
3. **A strong uniqueness title conceals unverified premises.** `justindbilyeu`'s main document assigns dimension4 to `Hom_Spin(Lambda2 tensor Cl, Lambda1 tensor Cl)` yet states the dimension still needs a LiE/Sage branching computation. It mixes a Lorentzian metric bundle with the Riemannian `GL(4)/O(4)` fiber in its setup. The suggested four displayed generators require degree/type checking before taking linear combinations. Its conclusion is not a completed proof we can reuse.

## Search coverage and exclusions

Search performed using web queries for GU software, GitHub, Mathematica and Python, plus GitHub repository search for exact phrase `geometric unity`. The API returned 12 candidates; its raw response is preserved in `metadata/github-search-geometric-unity.json`. Official author project pages and dissertation supplied the primary provenance. This search did not identify a separately downloadable, current, author-maintained GU code repository; that is a bounded search result, not a claim that none exists.

`ericqweinstein` is a different software engineer: the [Code BEAM biography](https://codebeamamerica.com/legacy-content/2017/eric-weinstein/) describes Hulu/Georgia Tech, not the GU author. GA-Unity is a Unity game-engine geometric-algebra package, also unrelated to the GU implementation sought. E8 quantization projects inspired by a podcast and broad GU-tagged AI operating-system projects are not author code or a demonstrated implementation of GU.

## Recommended exploration order

1. Reproduce the dissertation's six symbolic determinant fixtures with exact arithmetic and source-normalization notes; highest immediate value.
2. Formalize the bounded exterior/symbol lemmas in Lean, then the projection identities. This would connect an actual author-associated computational object to our existing algebraic library.
3. Build a typed source dictionary connecting thesis operator ingredients to GU's invariant tensors, without assuming the eight-dimensional elliptic construction is already the fourteen-dimensional dynamical operator.
4. Use community programs only as independently testable hypotheses and comparison fixtures. In particular, compare their exact input/output types, real forms and omitted maps before comparing conclusions.
