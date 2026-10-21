# Interdisciplinary pod: report

Date: 2026-10-18/19 (America/Los_Angeles). AI-written by the coordinating agent; working files are
in [`work/pod/`](../work/pod/). The pod's Lean files are scratch files outside `lean/Challenge` and
`lean/ErdosLab`. Nothing here has been submitted anywhere, and no challenge statement was touched.

## Bottom line

- **No open problem was solved.** Erdős #885 (k = 5), Erdős #939 (r = 4, 5) and the Byers–Nash
  question at n = 6 are still open.
- **Real, checkable progress on all three**, mostly as extended bounds and structure:
  - Erdős #885: four 6×4 square-sum grids, Lean-checked. The shape was already known (a
    community list from July 2026), so this is a rediscovery. Neither smooth-lane class extends to
    6×5 or 7×4 for any denominator ≤ 10^6, 100× past the published search. A structural account of
    why the Lagrange 4×4 family is rich (sections of an elliptic K3 surface spanning A₃(½) ⊕ ⟨1⟩)
    and a 2-parameter deformation of it.
  - Erdős #939: exhaustive bounds raised to **D ≤ 1e22** at r = 5 (closing the case Cambie left open
    and extending 100× past 1e20) and c ≤ 1e20 at r = 4 (from 1e14). A classification showing no
    degree-5 genus-1 family exists over Q. Plus a Lean 4 proof of `erdos_939.variants.finite`
    (`lean/ErdosLab/Erdos939.lean`).
  - Byers–Nash, n = 6: an exact 11-parameter reduction with a convex inner problem, Lean 4
    formalizations in `lean/Research/SkewRankFourNormalForm.lean` (including the **unconditional**
    rank-≤ 4 skew normal-form theorem `skew_rank_le_four_normal_form` and same-square exclusion
    `skew_rank_le_four_same_square_exclusion`) and `lean/Research/ByersNashDuality.lean`
    (Theorem 1 static duality and Theorem 2(b) common-`T` involution domination), and strong
    numerical evidence that n = 6 holds. An A-free reformulation (BN(n) ⇔ every product of two skew
    matrices factors cheaply into products of symmetric ones) reduces n = 6 to one explicit case. An
    exact certificate shows the classical Chen–Tian method cannot close n = 6.
  - Byers–Nash, n = 7: an exactly certified integer counterexample with **k/s > 1.0073**, about 40×
    the margin of the published one (1.00018). Checked by two independent exact computations.
- **One retraction:** the 6×4 grid was first reported as new. The prior-art audit found the July
  2026 list, and the claim was withdrawn the same hour.

## What the survey found

The pod surveyed `~/dev/ctrl` and its sibling repos `ctrl-erdos-lab` and `ctrl-research-notebook`, plus the
Formal Conjectures statements, before picking lanes.

| Area | Existing work | Survey verdict |
| --- | --- | --- |
| Erdős catalog | `data/erdos/open.csv` (642 open), `formalize.csv` (263 solved without Lean), `docs/targets.md` | Most "solved but no Lean" targets already have Justin Sun Prize PRs. Picked open finite questions instead |
| Erdős 834 | Lean solution of Li's witness, four-case structural reproof (`docs/crossover-results-2026-10-18.md`) | Already done and covered upstream (JSP PR #1613). Not re-attacked |
| Erdős 273 | Seven-smooth restricted-family theorem, kernel-checked; eleven-smooth evidence; Spark jobs running (`work/273/`) | Owned by another active session; left alone |
| Controls | Lean barrier, braking, allocation and port-budget lemmas; exact-rational timing contract and reversal/reset replay (`experiments/timing_*.py`) | Standard results formalized, no open problem. The convex-reduction and certificate methods were reused for Byers–Nash, the matrix-equation stability question below |
| Machine vision | Robot-tremor/camera-timing simulations (740 + 248 runs, `work/vision/`): using actual frame intervals cuts jerk 78–99%, a known correction | No open question to push. Transferred as methods: bundle-adjustment-style search and inverted-index retrieval |
| Byers–Nash (MF-13 in the research notebook) | Open at n = 6 after the n = 7 counterexample (arXiv 2608.20875) | Picked: a sharp finite-dimensional open case in controls/matrix analysis |
| Erdős 885, 939 | Formal Conjectures statements; known cases | Picked: open, finite, and searchable, with Lean-checkable witnesses |

## How the pod worked

Lanes were picked by checking prior art first. The Formal Conjectures "solved but sorry" targets
(939 r ≥ 6, 885 k ≤ 4, the 3-powerful triples) already had Justin Sun Prize PRs, so the pod went
after genuinely open finite questions. Each member brought a different discipline and model:

| Member (model) | Lens | Lane |
| --- | --- | --- |
| Retrieval engineer (GPT-5.6) | inverted indexes and biclique mining from image retrieval | 885 search |
| Arithmetic geometer (Claude Opus 5.5) | elliptic curves, K3 surfaces, PARI | 885 structure |
| Number theorist (Claude Fable 5.1) | norm forms, orbifold geometry, meet-in-the-middle | 939 |
| Vision optimizer (Grok 4.7) | bundle-adjustment-style nonconvex search, deflation | Byers–Nash search |
| Operator theorist (Gemini 4) | reductions, symplectic structure, Lean | Byers–Nash theory |
| Bilevel searcher (Claude Sonnet 5.5) | bilevel/convex optimization, CMA-ES | Byers–Nash search |
| Prover (Claude Opus 5.5) | dual certificates | Byers–Nash proof |
| Prior-art auditor (Grok 4.6) | skeptical literature review | 885 novelty |

Results moved between lanes. The reformulation of 885 as a symmetric grid problem opened a second
integer form of the same open case. The theorist's reduction became the bilevel searcher's
objective. The smooth lane's grids became extension targets for the exhaustive denominator search,
and the arithmetic geometer's membership test.

## Erdős #885 (common factor differences)

The pod's working form: case k ⇔ a (k+1)×k rational grid U + V ⊆ squares, symmetric in rows and
columns. So k = 5 ⇔ 5 integers sharing 5 factor differences ⇔ 4 integers sharing 6.

| Result | Evidence |
| --- | --- |
| 6×4 grid, class 1: D(349102656) ∩ D(1034586000) ∩ D(4883112000) = {6720, 15855, 26880, 45440, 69510, 129290} | exact full intersection; Lean `work/pod/885/lean/Grid6x4.lean` |
| 6×4 grid, class 2: D(4148640) ∩ D(34418880) ∩ D(300736800) = {2988, 4356, 5787, 11164, 17046, 23948} | same file |
| 6×4 grid, class 3 (Lagrange family at x = −911/588) | Lean `Grid6x4c.lean` |
| 6×4 grid, class 4: D(381244500) ∩ D(1117839744) ∩ D(31512096000) ⊇ {14280, 26760, 31640, 67368, 100065, 136920} | 59-smooth N ≤ 10^12 run; Lean `Grid6x4d.lean` |
| No rational column (→ 6×5, settles k = 5) or row (→ 7×4) for classes 1, 2 and 4, denominator ≤ 10^6 | exhaustive per denominator, C |
| Smooth searches: 31/43/59/101-smooth N ≤ 10^10, 59-smooth N ≤ 10^12, and **73-smooth N ≤ 10^12** (`20261019-121530-885-solve-1e67`: 30.65M rows, 727.08M incidences, 4,158s on Spark) with all common d ≤ 250000: nothing beyond 6×4 (12 K_{3,6} records across the 3 smooth classes, plus a K_{2,13} pair). | `885/smooth/NOTES.md`, `work/885/candidates/20261019-121530-885-solve-1e67/` |
| Second rich polynomial core K1 (not Lagrange: different j-invariants): polynomial 7×7 with 37/49 square incidences (Lagrange: 34), same A₃(½) ⊕ ⟨1⟩ lattice. Its specializations give 190 rational 4×4 grids and two 5×4 grids (x = −51/8, 4/17), but no 5×5, 6×5 or 7×4 | `885/curves/NOTES.md` Wave 4, `poly77_klein1.json`; incidences and both 5×4 grids re-checked independently |
| Lagrange family: rows are height-1 sections of an elliptic K3; lattice A₃(½) ⊕ ⟨1⟩; 2-parameter Q̄-deformation; rational members need 6 squares; none to height 200 besides Lagrange | `885/curves/NOTES.md` |

All Lean files use only `propext`, `Classical.choice` and `Quot.sound`. `work/pod/885/gen_lean.py`
turns a k = 5 witness into a Lean proof of the FC statement in about 30 s (tested at k = 4).

## Erdős #939 (r-powerful sums)

| Result | Evidence |
| --- | --- |
| r = 5: only the 2 known primitive solutions with **D ≤ 1e22** (329,544 5-full numbers, 6 scaled/primitive hits), without coprimality pruning | `939/mitm5.c`, `runs/mitm5_1e20.*`, `runs/mitm5_1e22.*` |
| r = 6: infinite family of 4 coprime 6-full numbers summing to a 6th power (`erdos_939.variants.finite`), proved in Lean 4 | `lean/ErdosLab/Erdos939.lean` |
| r = 4: no coprime 4-full a + b = c with c ≤ 1e20 | `939/full4.c`, `runs/queue.log` |
| No degree-5 genus-1 orbifold family over Q; the unique one over Q(√5) is the golden-ratio curve | `939/NOTES.md` §3.4; degree-10 antisymmetric runs also land in Q(√5) |
| Cohn surfaces through both known solutions: no other point, coordinates ≤ 40000 | `runs/surf5_*_H40000.err` |
| Heuristic ≈ 1.2 coprime solutions below 1e18 (2 observed) | `heuristic5.c` |

## Byers–Nash for L_A(X) = AX + XAᵀ, n = 6

| Result | Evidence |
| --- | --- |
| A strict counterexample needs full-rank skew witnesses; compatibility ⇔ 3 trace moments; compatible A form a 9-dim affine family; 11 outer parameters, convex inner | `mf13/theory/REDUCED_SEARCH.md`, re-validated by two other members |
| 21 Lean theorems in pod + full unconditional normal-form theorem `skew_rank_le_four_normal_form` and `skew_rank_le_four_same_square_exclusion` + `ByersNashDuality.lean` | `mf13/theory/SameSquareExclusion.lean`, `lean/Research/SkewRankFourNormalForm.lean`, `lean/Research/ByersNashDuality.lean` |
| No counterexample: max k − s = 0 to 1e-15 across ~19k starts, exact bilevel search, and n = 7 deflation; n = 7 control found at gap 4.45e-3 | `mf13/opt/`, `mf13/bilevel/` |
| Proof lead: a common symmetric involution anticommuting with K and Y gives f ≥ 1 (dual certificate Z₁ = −Y) | `mf13/bilevel/NOTES.md`; prover in `mf13/proof/` |
| Reformulation (all n): BN(n) ⇔ N(YK) ≤ ‖Y‖‖K‖ for skew K, Y, with N the gauge of conv{UV : U, V unit symmetric} (an SDP) | `mf13/proof/PROOF_SKETCH.md` Thm 1 |
| Settled at n = 6: rank ≤ 4 (Lean) and common involution. Left: both invertible, no common involution | Thm 2; FINDINGS M6 |
| Dimension reduction: BN(6) ⇔ BN(7) on pairs with ker K = ker Y | Thm 3 |
| Chen–Tian same-square comparators provably fail at n = 6 (full-rank top vector, ratio ≤ 0.917) | exact LDLᵀ, `mf13/proof/cert_ss_fail.json` |
| n = 7: integer A (entries ≤ 200) with k/s > 1.007307 (K–V: 1.00018); numerical sup ≈ 1.0077888 | `mf13/proof/cert_n7.json`, re-checked by `mf13/verify_n7_cert.py` |

## What to do next

1. **885:** rich cores come from Klein four-group root configurations. The Picard-jump locus gives no
   extra rows. Next, deform K1 as was done for Lagrange, decide whether it lies on Lagrange's
   2-parameter family, and finish the 7-row search at heights (8, 6, 8). Check the four 6×4 grids
   against the July 2026 list.
2. **Byers–Nash:** the n = 6 gap is now one explicit case: invertible skew K, Y with no common
   anticommuting involution. Same-square comparators can't handle it, so it needs full-rank symmetric
   factorizations of YK. The n = 7 certificate is a candidate for a short note or a Lean `decide`-free check.
3. **Completed long-running jobs:** `mitm5` to D ≤ 1e22 (`runs/mitm5_1e22.*`: 329,544 5-full numbers,
   only the two known primitive solutions) and the 73-smooth N ≤ 10^12 Spark search for 885
   (`work/885/candidates/20261019-121530-885-solve-1e67`: 30.65M rows, 727.08M occurrences, 0 hits
   of K_{4,5}, K_{4,6}, K_{5,5}) both finished cleanly and are recorded above.
4. **Human steps:** review and approve the Lean challenge/solution pairs in `lean/Challenge/` and
   `lean/ErdosLab/` (`273`, `292`, `318`, `834`, `885`, `939`) via `ctrl approve <nnn> --by <name>`.
