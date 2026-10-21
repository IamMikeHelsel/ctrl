# Clebsch supplement: split one seed neighbor, then use an explicit edge motif

Exact finite test, independently labeled using the16 odd-parity five-bit words, with edges at Hamming distance4. This is isomorphic to the usual Clebsch representation; neither original source nor other role's files are modified.

Seed v has word1 and neighborhood `{14,22,26,28,31}`. Exhausting all65536 cuts gives the following spectrum of maximum crossing count by k retained seed neighbors:

| k | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| Maximum crossing, unrestricted seed side |29|32|29|29|32|29|
| Maximum crossing, seed fixed outside |24|29|28|29|32|29|

There are40 edges and target internal cost `512/47`; integer acceptance requires crossing≥30. Consequently at least one seed neighbor must leave the initial side, and removing exactly one is sufficient with the rest optimized. Removing two or three cannot meet the target, even with unrestricted remaining choices. Complement symmetry explains the unrestricted k=1/k=4 agreement.

An explicit positive witness removes word31 and adds words `{2,4,8,16}`. The resulting side is `{2,4,8,14,16,22,26,28}`, crossing32 and internal8. Removing word31 from the untouched neighborhood alone instead gives internal20. Thus “one removed seed neighbor suffices” does not mean a single vertex flip from the original neighborhood solves the fixture.

The positive witness has a useful structured description: let w=31, which is adjacent to v=1. Then

`S=(N(v)∪N(w)) \ {v,w}`.

Every one of the40 Clebsch edges supplies such a cut of cost8. No global rest optimizer is required for this motif. For any simple triangle-free graph and edge vw, the sets `A=N(v)\{w}` and `B=N(w)\{v}` are disjoint and individually independent. Hence its exact crossing count is

`C(v,w)=Σ_(u∈A∪B) d(u)−2 e(A,B)`.

Here `e(A,B)` is the number of four-cycles through edge vw. Summing over all edges yields the general hand identity

`Σ_(vw∈E) C(v,w)=2Σ_(vw∈E)d(v)d(w)−Σ_v d(v)²−8 #C4`.

The factor8 arises because every four-cycle contains four edges, and each motif subtracts twice its edge-specific count. In Clebsch the two degree terms are2000 and400, and `#C4=40`, so total crossing1280, average32. This identity is a new candidate feature/move in this campaign, not a novelty claim. It is not uniformly strong: in the ordinary cube all such edge motifs have crossing8 and internal4, above its target, while the graph is bipartite and has a zero-cost cut.

Recommended next test: combine the adjacent-edge endpoint-removal family with the domain's neighborhood extensions and an explicit bipartite recognizer, then seek a small triangle-free counterexample before attempting any uniform inequality. Any optimizer-produced multiplier must be separately checked and bound to the original cut semantics.

Evidence: `inventor_seed_split.py/json` enumerate the full finite spectrum, test all40 edge motifs and the double-counting identity. The general graph identity is hand-derived, not Lean-checked. Quality19/20; subjective confidence98% in these scoped conclusions, with the original general bound still unresolved.
