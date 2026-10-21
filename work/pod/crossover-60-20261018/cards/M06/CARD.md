# M06 — Missing middle-density cut certificate

**GO for a bounded seed-splitting and joint-motif certificate experiment. The universal middle-density theorem remains open.** AI-written; root PM plus domain, inventor and independent critic, all inherited root models with exact runtime identifier unavailable. No model-family diversity claimed, no remote inference.

Original question: Can a new exact graph constraint close the triangle-free cut bound2/47 in the remaining density interval8/47<2m/n²<49/125 without an unverified BCL premise?

The quantity is the **sum of internal edges in both parts of an unrestricted cut**, equivalently edges removed to make a graph bipartite. It is not a cardinality-n/2 induced subset problem. Selection title retains the old sparse-half context, but the frozen question and experiments use the cut quantity.

Provenance: `research/pods/2026-10-17/erdos/grade-01.txt` and `round-summary.txt` under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/`. Frozen source hashes are in roster.json. Prior independently reviewed work accepted hand epsilon descent and neighbor-cut high-density reduction; the exact BCL coefficient/PSD witness was missing. Existing source files and approved challenges remain unchanged.

## Prior art and recovered obstacle

[Balogh, Clemen and Lidický, Max Cuts in Triangle-free Graphs](https://arxiv.org/abs/2103.14179) reports2/47 and stronger density-specific results. Its source explicitly encodes many local rooted cuts and warns about the Clebsch graph. This campaign neither disproves that paper nor reproduces its missing flag-algebra data. Our edge-rooted constructions fall within the broad local-cut approach already described there; novelty is not established. [The Andrásfai special-case paper](https://arxiv.org/abs/0907.3928) means those family fixtures are calibration, not new family theorems.

The earlier branches cover r≤8/47 and r≥49/125. Uniform finite-error control still matters: a fixed numerical slack or a finite list of graphs cannot be converted into a universal bound. The previous epsilon descent is not re-proved here.

## Creative transfers and tests

**1. Robust multipliers and degree moments.** Retain degree variance in the exact neighbor-cut average rather than discarding it through Cauchy–Schwarz. With S2=Σd(v)², average crossing is S2/n; sufficient target admission is variance/n²≥r/2−r²−2/47. Regular graphs retain zero variance, so this alone cannot close the gap. Independent positive-gain flips in a second neighborhood improve Petersen internal cost6→4, but fail on Clebsch: best crossing29, internal11/256>2/47.

The failure is stronger than one heuristic: all2048 extensions of a fixed Clebsch neighborhood have crossing≤29; automorphisms transfer this to every root. Hand multi-affine rounding transfers the obstruction to uniform blow-ups. Any route keeping an entire neighborhood on one side therefore misses this fixture. Domain kernel edge-gain algebra and conditional moment averaging are separate from the hand graph-count bridge.

**2. Unexpected transfer: coding theory as a cut witness.** Clebsch vertices can be even-parity five-bit words, adjacent exactly at Hamming distance4. Every edge is internal in exactly one of the five coordinate cuts. Thus the five weighted internal costs sum to total edge weight m; one is≤m/5. For an arbitrary input graph with a validated homomorphism to this code graph, r≤20/47 implies cost≤2n²/47, covering the entire frozen middle interval. Kernel proofs bind actual40-edge code identities, arbitrary finite weighted-edge double counting and averaging. Three unequal blow-up weight fixtures and independent semantic mutations check the representation.

The mapping assumption is substantial. The explicit23-vertex twofold Mycielski(C5) graph has71 edges and density142/529 in the gap. A kernel palette-elimination proof shows it has no4-coloring; a checked4-coloring of the target code graph therefore rules out any homomorphism into that target. The71 hypotheses are independently bound to freshly constructed graph edges. The graph itself has an explicit cut of internal cost20<1058/47, also kernel checked; this is a limitation of the code route, not a counterexample to the original bound. An initial finite-decision proof exceeded the default heartbeat budget and is preserved; its failed sorryAx output was never accepted. The repaired proof uses omega and permitted axioms. An earlier DSATUR search status is diagnostic only, not the accepted proof.

**3. Energy landscapes and frustrated cycles.** A bad cut on the bipartite cube Q3 has internal cost4>128/47 but no improving one- or two-vertex move. In its balanced k-blowup, cost4k² still exceeds target and the first improving move has exactly2k+1 vertices. The hand bound Δ≥ks−s²/2 rules out every move of size≤2k; an explicit cross-component move attains improvement at2k+1. This defeats any fixed local-search radius as a uniform certificate, even for bipartite graphs. Supporting scalar inequalities are kernel checked; the general graph construction is hand-bound and independently reviewed.

For Wagner M8, a supplied cost2 cut and a rational packing of16 odd cycles, weight1/8 each, certify optimum2 by a hand double count. A producer-independent exact consumer rejects four corrupted receipts. The lower certificate does not require enumerating all cycles. Conversely, merely hitting all odd cycles does not make a proposed edge pattern a cut: a C4 with one internal edge is the negative control. These Python/hand results are not a Lean cycle-packing theorem.

**4. A concrete seed-splitting repair.** Exhaustive Clebsch cut spectra by the number of retained seed neighbors are[29,32,29,29,32,29]. Removing exactly one of five neighbors can reach crossing32; retaining all five cannot. The positive fixture has a simple motif: for an edge vw use S=(N(v)∪N(w)) minus both endpoints. Every Clebsch edge gives internal8. It fails standalone on the cube, so it must be combined with other valid cuts.

For this open-neighborhood union, average crossing over edges is

`U=(2 Σ_edges d(v)d(w)−S2−8 C4)/m`.

For the opposed-neighborhood cut with leftover vertices assigned independently and fairly, average expected crossing is

`F=m/2+(S2−m+4 C4)/(2m)`.

Root and inventor independently derived U; the critic audits both. All6228 labelled triangle-free graphs of orders1–6 pass both identities and their exact cancellation. The combination(1/5)U+(4/5)F cancels C4, but discards useful information: its Clebsch internal bound62/5 exceeds512/47 while the actual U cut costs8. This is a useful failed multiplier, not a universal proof. Keep the two valid constraints and their correlation rather than blindly eliminating the motif.

## Evidence, decision and next gate

Attributable reports: `domain.md`, `inventor.md`, `inventor_seed_split.md`, `critic.md`. Accepted kernel modules, hashes, axiom sets and independent replay results are recorded in `critic_acceptance.json`. No numerical solver assertion is accepted as a theorem. Whole-graph cut and blow-up bridges are marked hand-derived where not formalized; n≤6 coverage is finite corroboration. The new cut constructions do not supply a BCL PSD witness, a general middle-density result or a new extremal constant.

PM GO is for an informative next experiment, while whole-neighborhood retention and fixed-radius-only certification are NO-GO as universal routes. After all60 initial reviews, spend30minutes on a typed, independently checked joint family of seed-splitting cuts and exact degree/C4 constraints. Predeclare20 fixtures/mutations, including Clebsch and Mycielski blow-ups, graph-coordinate changes, duplicate/missing edges and invalid label maps. Require exact nonnegative multipliers and explicit uniform finite-error accounting before claiming density-interval coverage; otherwise retain a named obstruction.

Quality rubric: faithfulness4/4, reproducibility4/4, discrimination4/4, independent critique4/4, actionability3/4 = **19/20 (95%)**. Subjective confidence is high in the scoped obstructions/certificates; chance of closing the universal gap is unquantified. No physical validation is relevant or claimed.
