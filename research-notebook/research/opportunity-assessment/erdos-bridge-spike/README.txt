Erdos 128: bounded graph deletion/restoration bridge
2026-10-17

Result
DeletionBridge.lean proves a useful graph-level component of the newer proposed
sparse-half argument. It is ordinary finite-graph mathematics newly connected
to the existing formal interfaces here, not a new extremal bound, a solution
of Erdos128, or a prize claim.

Let G be any finite simple graph, X a finite vertex subset, and H the graph
obtained by deleting precisely the edges whose two endpoints belong to X.
For every rational vertex-weight function x with 0<=x(v)<=1, the file proves

  edgeCost_G(x) = edgeCost_H(x)
                 + sum_{uv in E(G), u,v in X} x(u)*x(v),
  edgeCost_G(x) <= edgeCost_H(x) + e_G(X).

Every edge is an unordered pair and counted once. X.sym2 contains diagonal
pairs, but a simple graph has no loop edges, so they contribute nothing.
The cost convention is the EXACT upstream Erdos128.edgeCost, not a separately
defined objective presumed equivalent. edgeCost_eq_sum proves the connection
from its symmetric bilinear expression to the product x(u)*x(v).

The main reusable theorem is
  Erdos128.DeletionBridge.restore_fractional_half:
    HasFractionalHalfBound (deleteInside G X) B ->
    HasFractionalHalfBound G (B + (edgeCountOn G X : Q)).

It reuses the SAME weight vector and total mass. The fractional-half predicate
requires weights in [0,1] and sum x=|V|/2, including odd vertex counts. No
integral floor-half extraction is asserted by this new file.

Also proved: X is independent in H; every CliqueFree k property of G persists
in H, in particular triangle-freeness. These establish the actual graph
preconditions for applying a completion theorem to H.

Seven new audited lemmas
- edgeCost_eq_sum
- pairWeight_bounds
- deleteInside_independent
- deleteInside_cliqueFree
- restoration_identity
- restoration_bound
- restore_fractional_half

The existence of the fractional half in H is an EXPLICIT theorem premise.
No completion theorem, max-cut theorem, or new mathematical axiom is declared.
The restoration identity and bound do not themselves require triangle-freeness.
Dividing the displayed inequality by n^2 for n>0 gives the informal paper's
additive q=e_G(X)/n^2; this normalized corollary is not separately encoded here.

What remains for the proposed 2587/100000 bound
1. Supply the independent-set completion bound on the modified graph, including
   the extended independence-ratio interval [1/3,3/8]. This is the substantive
   missing graph theorem; the existing rational polynomial identities do not
   prove it.
2. Supply and explicitly track the Balogh-Clemen-Lidicky max-cut hypothesis
   (or prove the cited result), then connect both graph constructions to the
   scalar envelopes. The inherited library currently treats BCL as a premise.
3. Connect to the pre-existing rounding theorem for a floor(n/2)-vertex set.
4. Independently review the proposed mathematical improvement against literature.
The .02587 value is still a separate author's claimed partial bound. None of
these files proves the Erdos1/50 target or establishes priority for the claim.

Upstream provenance and API comparison
GraphBasics.lean is copied byte-for-byte from:
https://github.com/aimir/erdos-128-sparse-halves
commit ba85f319ebb33ec2194ef4c2929a12916329e1e7
path lean/Erdos128/GraphBasics.lean
SHA256 ddf949f92df8c1b69140d43b8f03337f1fa6300ef761ce9572aabc66d278bce8
The upstream project pins Lean4.30.0. Only this copied GraphBasics module was
ported by compatibility checking: it compiled UNMODIFIED on installed4.35.0.
The full upstream library was not built in this experiment.

The argument under study is Section3 of:
https://github.com/pma1999/erdos-128-sparse-halves
commit2193a4a06a4ec288a53ae986cdca5c1082abf1bb
path outputs/cut-independent.tex
This author supplies the proposed delete/complete/restore combination; this
spike claims formal glue only. The inspected upstream GraphBasics already
provides the cost convention, indicator/count identity, bilinear operations,
nonnegativity and independent-support zero cost. Its RoundingFinal module
already provides fractional-to-floor-half rounding. A narrow upstream source
search found no deleteEdges/deleteInside/restoration implementation, which is
not a global novelty search. Mathlib already supplies graph edge deletion,
clique-free monotonicity and finite-sum splitting; our proof composes them.

Reproduction and trust boundary
Run from any directory:
  python3 /absolute/path/to/erdos-bridge-spike/verify.py
Optional --toolchain-bin selects an already installed compatible toolchain.
The runner never downloads or installs dependencies, and never edits the
upstream clones or controls project. It uses the controls project's existing
pinned package cache, EXCLUDES original controls project .oleans from LEAN_PATH,
freshly compiles the copied GraphBasics and new bridge, audits all seven new
theorems, then invokes leanchecker for both local modules.

verification.json records exact source hashes before/after, toolchain, mathlib
commit, commands, timing, logs, axiom closures and exit codes. Both modules are
kernel-replayed into their imported environments. Cached mathlib/package
artifacts remain trusted; this is NOT a fresh replay of all mathlib and is not
verification by an independent prover. leanchecker uses Lean's own kernel.
All seven accepted new theorem closures contain only propext, Classical.choice,
and Quot.sound. Harmless unused-section-variable warnings do not change scope.

Development note: an attempted leanchecker --help invocation was stopped after
discovering that this tool has no help flag and instead begins default-module
processing. The recorded verification uses explicit module targets only.

Next bounded research action
The infrastructure is now sufficient to state the missing independent-set
completion contract using the real graph objective. The next useful experiment
is a source-faithful formalization of ONE completion branch, with its actual
graph construction and averaging argument. Do not keep polishing this standard
restoration identity or run another small finite census as a substitute.
