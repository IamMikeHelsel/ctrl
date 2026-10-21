# M06 independent critique

GO for an exact cut-certificate consumer and a broader family of graph-level cuts. HOLD the universal middle-density theorem. NO-GO for treating bounded local optimality, degree variance alone, or a single Clebsch code map as universal coverage.

## Faithful question and source

The frozen quantity is the number of unordered edges INTERNAL to an unrestricted two-part cut, divided by n². It is not a balanced-half induced-edge objective. The density is r=2m/n², not m/binom(n,2). The saved grade's low/high branches and unresolved interval are preserved; no BCL data package or unverified premise is used here. The existing finite enumeration does not supply a uniform asymptotic error bound.

The explicit Andrásfai examples are calibration, not a novelty claim. [Heinig's 2009 paper](https://arxiv.org/abs/0907.3928) already provides a family bipartification of size floor(k²/4). This review independently enumerates the small fixtures; it does not infer global optimality merely from that paper's inclusion-minimality terminology.

## Exact finite evidence

`critic_graphs.py` reconstructs each graph and checks triangle-freeness, actual crossing counts, neighbor-degree sums and all cuts modulo complementation. Andrásfai k=3,4,5,6 have r=3/8,4/11,5/14,6/17 and zero degree variance. Their best neighbor cuts leave 3,6,10,15 internal edges, while unrestricted minimum internal costs are 2,4,6,9. These regular middle-density graphs expose the limitation of the degree-variance gate without challenging the desired cut theorem.

For the Clebsch graph reconstructed independently as 16 four-bit strings joined at xor weight 1 or 4, every one of the 256 two-neighbor candidates has at most 29 crossing edges. Its internal cost 11 exceeds 2n²/47 by normalized 5/12032. Unrestricted exhaustive cuts attain 32 crossing edges, hence internal cost 8. The stronger independent 2,048-case test shows EVERY cut side containing N(0) has crossing count at most 29. Translation symmetry extends this to every root. Thus merely adding vertices to a complete neighborhood cannot repair this fixture. The ten outside non-root vertices have independence number 4; the extension gain's internal-edge penalty is essential.

A triangle mutation breaks the neighbor crossing/degree-sum identity. Density normalization and explicit edge uniqueness are checked separately.

## Local-search obstruction

The cube cut by parity of its first two coordinates has 8 crossing and 4 internal edges, so normalized internal cost is 1/16>2/47. Every one-vertex flip strictly worsens it, and every two-vertex flip is nonimproving; a three-vertex move improves it. The graph itself is bipartite and has internal optimum zero.

The inventor's stronger balanced t-blowup argument was independently checked. Each vertex initially has crossing-minus-internal degree t. For a flipped set with a and b vertices on the two cut sides, its cost change is

    t(a+b) + 2 e_internal(S) − 2 e_cross(S).

Since e_cross(S)≤ab and 4ab≤(a+b)², every set of at most 2t vertices is nonimproving. A set of sizes t and t+1 inside one crossing K_(2t,2t), with no internal edges, improves cost by t. The first improving radius is therefore 2t+1. Every fixed local radius fails uniformly as t grows, while density remains 3/8 and bad normalized cost remains 1/16. This is a route obstruction, not a lower bound on the optimal cut. Scalar Lean lemmas check the arithmetic; the general graph/blowup binding is an explicit hand argument.

## A positive code certificate and its boundary

Root's five-bit labels give each edge Hamming distance four. Therefore each edge is internal to exactly one of the five coordinate cuts; their total cost equals m, and at least one costs at most m/5. This is an exact finite identity, with no sampling collision or asymptotic error. It extends edgewise to arbitrary nonnegative edge weights and to a graph supplied with a valid homomorphism, including unequal blowups. Labels need not be injective on independent vertices.

An independent consumer verifies all 40 edge identities, all five costs 8, three weighted examples, and an explicit isomorphism to the separately reconstructed folded-cube graph. It rejects altered label bits, out-of-range high bits, duplicate edges, loops and missing labels. The density condition r≤20/47 covers the frozen middle interval PROVIDED the labeling exists. That proviso is substantial.

The target has the independently verified four-color map [0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3]. The 23-vertex double Mycielski lift of C5 is not four-colorable: remove the apex color by replacing each original vertex carrying it with its shadow's color, twice; this would two-color C5. Root's two literal 71-edge hypothesis lists were independently matched to a newly generated graph. Kernel replay is tracked separately in the acceptance file; DSATUR failure alone is not accepted evidence. The graph nevertheless has an explicit passing cut with 20 internal edges, since 47·20<2·23². Its inability to map to the target is only a certificate-family limitation.

## Edge-rooted moment transfer

The two complementary edge-rooted constructions were independently checked on all 434 nonempty labeled triangle-free graphs of order at most five. The critic explicitly enumerated every fair leftover assignment, rather than reusing the producer's expected-cost formula. The 1/5 open-union and 4/5 opposed-neighborhood mixture cancels C4 and yields internal cost at most 3m/5+2/5−(S2+2Σ_(uv in E)d_u d_v)/(5m). The finite +2/5 term cannot be discarded: doing so claims a negative internal bound −1/5 on K2. This exact finite identity remains too weak on the Clebsch fixture and does not close the middle interval. A future multiplier search must retain actual cut semantics and finite errors.

## Formal acceptance

37 printed declarations independently compile with permitted axioms or no axioms: critic 4, domain 9, inventor 4, and root 20. The repaired Mycielski proof proves nonexistence of the specified homomorphism without trusting DSATUR. Its literal 71-edge assumptions and all 23 adjacency rows were checked against independent graph construction. Weighted cut averaging is kernel-checked for the supplied target adjacency; arbitrary source-graph map existence is not proved. Failed drafts are retained and excluded. The critic's first Lean draft used an unavailable Finset API; its repaired version passes and the domain worker independently replays it.

## Gate and limitations

Next, test a certificate family that can remove as well as add neighborhood vertices, or admit complete graph-level code/weighted-cut receipts with explicit fallback coverage. Keep graph identity, edge orientation/uniqueness, weights, normalization, cut realizability and family coverage bound to the receipt. A negative mapping search is not a no-cut theorem. Odd-cycle hitting alone does not characterize a cut: a C4 with one edge designated internal satisfies no odd-cycle restriction but violates cut parity.

All source files and approved challenges remain unchanged. No integrated CLI change is proposed. Quality: 18/20 for the scoped audit. Confidence is subjective and high for the exact finite identities and counterexamples; no probability of resolving the universal theorem is claimed.
