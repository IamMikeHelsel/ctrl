# M06 inventor: local traps, cut codes, and missing graph features

AI-assisted research. Runtime: inherited root model, exact identifier unavailable. Original source inspected: `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/erdos/grade-01.txt`; campaign frozen roster and charter. No novelty claim or new literature attribution is made.

The exact question remains: every finite simple triangle-free graph should admit an unrestricted vertex cut whose **sum of internal edges in both parts** is at most `2n²/47`; the accepted elementary branches leave `8/47<r=2m/n²<49/125`. This review supplies a general obstruction to one proposed proof route and small exact certificates, not that theorem or a replacement BCL premise.

## Transfer 1: robust multipliers and missing state variables

Map a graph to density, degree second moment, and codegree/motif features, analogous to an uncertain system summarized by moments. A nonnegative combination of graph-valid inequalities can certify a cut upper bound only if the cut semantics and feature identities are valid for every graph, with uniform finite-size corrections. The existing neighbor-cut identity improves the density-only estimate by degree variance:

`cost/n² ≤ r/2−r²−Var(degree)/n²`.

Preserved object: an actual neighborhood cut, not a relaxed pseudo-distribution. Failure boundary: degree variance is zero in regular graphs, and arbitrary moment vectors need not be realized by graphs. A PSD/multiplier solver cannot fill those semantic gaps.

Exact discriminator: cube Q3 and Wagner/Möbius ladder M8 both have eight vertices, twelve edges, degree sequence `(3,…,3)`, and `r=3/8` in the missing interval. Both have best neighborhood-cut internal cost 3, above `128/47`. Their actual optimum internal costs are respectively 0 and 2. Thus these degree statistics cannot distinguish their frustration; codegrees or larger motifs are meaningful next features. This does not prove that no degree-based uniform theorem could exist, merely that the existing neighbor/variance branch has identical slack here. The domain researcher separately develops the variance and two-neighborhood route.

Falsifier for a new multiplier: exact evaluation on these fixtures and on the domain's obstruction graphs, followed by verification that each inequality has a graph proof. A successful finite screen remains a candidate, not a uniform certificate.

## Transfer 2: Ising metastability versus a uniform cut theorem

Give each vertex a binary spin and charge an edge when its endpoints agree. Flipping a set S changes the internal cost by

`Δ(S)=Σ_{v∈S} δ_v +2 e_internal(S)−2 e_cross(S)`,

where `δ_v` is the one-vertex flip cost. This preserves the original unrestricted cut objective exactly. Local stability is a statement about a specific cut, not global optimality or the existence of another good cut.

In Q3, mask60 gives cost4 while the global cost is0. In M8, mask85 gives cost4 while the global cost is2. Both bad cuts have every singleton flip cost +1, every two-vertex flip nonnegative, and an improving three-vertex move. Thus even two-vertex local optimality does not imply the target on eight vertices.

More strongly, form the balanced k-blowup of Q3, retaining the bad cut's cluster signs. The graph remains bipartite and triangle-free, with `n=8k`, `r=3/8`, optimum0, and bad cost `4k²`, normalized `1/16>2/47`. Every singleton flip cost is k. For any set S of size s, split S by the current cut into sizes a,b. Its crossing edges number at most ab; hence

`Δ(S)≥ks−2ab≥ks−s²/2≥0` for `s≤2k`.

One crossing component is `K_(2k,2k)` with no internal edges. Select k vertices on one side and k+1 on the other. Then `s=2k+1` and `Δ=−k`. Therefore the first strictly improving cardinality is exactly `2k+1`. **Every fixed local-flip radius fails uniformly**, even in bipartite graphs at a density inside the unresolved interval. This does not preclude local search with neutral moves, graph-sized cluster moves, or a theorem proving that some other initial cut is good.

Exact experiments instantiate k=1,2,3,4; all moves of sizes up to2k are exhausted for k≤2 (36 and2516 moves). Larger k uses the displayed general hand argument, not a finite extrapolation. A scalar Lean file checks the counting-inequality consequences; the graph-to-count binding is hand-derived and separately critiqued.

Falsifier/next step: require a proposed local-improvement theorem to explain these blowups. A promising alternative move family must scale with graph structure, rather than have a fixed vertex budget.

## Transfer 3, deliberately unexpected: a cut is a syndrome-decoding solution

Map each edge to an internal-edge bit y. For every cycle C,

`Σ_(e∈C) y_e = |C| (mod2)`.

These constraints express that crossing-edge bits form a cut. Conversely, on each connected component, satisfying all fundamental-cycle equations permits reconstruction of vertex labels along a spanning tree. Thus minimum internal edges is a minimum-weight solution in a binary affine code. The mapping preserves exact graph cost and global consistency; it imports neither an efficient general decoder nor an extremal bound.

A useful certificate pair is asymmetric: an explicit vertex cut gives an upper bound, while rational nonnegative odd-cycle weights with edge loads≤1 give a lower bound. Every odd cycle contains an internal edge, so summing the weighted inequalities is sound. The listed cycles need not be exhaustive. This permits a small producer-independent certificate consumer instead of trusting an optimizer or exhaustive-search verdict.

On M8, all16 supplied simple odd cycles weighted1/8 have edge loads≤1, giving lower bound2. A cut of cost2 attains it. `inventor_cycle_consumer.py` separately verifies each cycle is connected, 2-regular and odd, computes edge loads, and checks the supplied cut. It rejects deleting a cycle while retaining the lower-bound claim, overweighting, replacing a cycle by a single edge, and substituting the bad cut. Petersen's all-odd-cycle uniform packing only gives2, while its exact optimum is3: this particular relaxation is not automatically tight.

Negative control: C4 has no odd cycles. An edge-label vector with exactly one internal edge satisfies vacuous odd-cycle hitting but violates its even-cycle parity and is not any cut. A lower-bound packing must not be confused with a complete representation of feasible cuts. Rational packing is Python-exact here, not a Lean-checked solver certificate; it is not promoted as a formal result.

## Semantic trap and evidence

Balanced cuts are a different objective. In K1,5 the unrestricted internal optimum is0, but every balanced 3/3 cut has internal cost2, exceeding `72/47`. This is not a counterexample to the original unrestricted theorem, nor to a problem counting only one half's induced edges. The certificate must name the objective explicitly.

Artifacts: `inventor_graph.py/json`, `inventor_blowup.py/json`, `inventor_cycle_consumer.py/json`, and `inventor_locality.lean`. All graph and rational arithmetic tests pass; the critic independently confirmed the cube obstruction, including the sharp2k+1 escape radius. Lean compilation status is reported separately when complete. No source or approved challenge was edited.

Recommended PM split: NO-GO for “bounded-size local optimality alone certifies2/47.” GO for a bounded study of graph-sized neighborhood/cluster moves and exact cycle/cut certificate consumers, evaluated against the regular graph obstructions. HOLD the original all-graphs theorem until a graph-valid uniform argument or exact faithfully bound certificate is supplied. The cycle lower certificate is diagnostic evidence, not progress by itself on the needed upper bound.

Quality rubric: faithfulness4, reproducibility4, discrimination4, critique4, actionability3 =19/20. Subjective confidence:98% in the scoped cut calculations and hand blowup obstruction; no calibrated probability of closing the original theorem is claimed.

Compilation update: `lake env lean ../work/pod/crossover-60-20261018/cards/M06/inventor_locality.lean` exited0. All four printed declarations use only `propext`, `Classical.choice`, and `Quot.sound`. These prove the scalar subset inequality, larger-subset arithmetic, target comparison, and middle-density placement; they do not kernel-check the graph family construction or general cut-space theorem.
