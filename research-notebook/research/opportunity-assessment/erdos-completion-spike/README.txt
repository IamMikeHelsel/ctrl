CURRENT STATUS: see FINAL-STATUS.txt for the assembled all-finite-order,
integral theorem conditional only on the explicit published BCL input.
This file retains the earlier checkpoint or source-inspection record.

Erdos 128: finite graph completion components
2026-10-17; bounded continuation of the checked DeletionBridge spike.

RESULT / LIMIT
This directory formalizes actual finite-graph constructions from the proposed
2587/100000 sparse-half argument. It does NOT establish that global bound,
prove Erdos 128, establish new extremal theory, or claim a prize. The project
uses rational profiles and the exact upstream Erdos128.edgeCost convention:
unordered simple-graph edges, each counted once, weight product at endpoints.

CHECKED COMPONENT MAP (see completion-verification.json for final status)
CompletionBranch.lean (7 public theorems)
- cross_indicator_eq_degree_sum: twice the symmetric cross form is the sum
  of actual B-degrees over E. Overlapping supports count incidences correctly.
- independent_extension_cost: if E is independent and disjoint from B,
  e(B union E)=e(B)+sum_{u in E}deg_B(u).
- exists_neighborhood_completion: in a triangle-free G, if disjoint D has
  at least m neighbors of v and every D-vertex has B-degree <=q, select m of
  those neighbors and obtain S containing B, |S|=|B|+m,
  e(S)<=e(B)+m*q. No low-cost existence conclusion is assumed.
- fractional_half_of_neighborhood_completion: when 2*(|B|+m)=|V|, the selected
  S gives an actual rational [0,1] profile of total |V|/2 with the same bound.
- heavy_neighbors_independent: all vertices with 2*deg_B(v)>|B| are independent.
  The proof obtains a shared B-neighbor, then uses triangle-freeness.
- exists_low_degree_candidates: given an upper bound a on every independent
  set, constructs D disjoint from B with |D|=|V|-a-|B| (natural subtraction)
  and deg_B(u)<=|B|/2 for every u in D. The zero-size possibility is explicit;
  the paper's eventual application still needs a+|B|<|V| for a nonempty D.
- restore_neighborhood_completion: applies the actual construction to
  H=G with X-internal edges deleted, then invokes restore_fractional_half.
  The final cost in G is e_H(B)+m*q+e_G(X).

GreedyExtension.lean (2 public theorems)
- edgeCount_insert proves the exact increase when adding one new vertex.
- exists_greedy_extension constructs B superset A up to target size t with
  e(B)<=e(A)+k*(|B|-|A|), and either |B|=t or all outside B-degrees exceed k.
  The existence proof maximizes cardinality among feasible extensions.
  It has no independent-set or triangle-free assumptions because none are
  needed for this general stopping statement. A is a concrete feasible seed.

AveragingBridge.lean (3 public theorems)
- weighted_neighborhood_double_count proves the actual incidence identity.
- neighborhood_size_sum counts the B--D incidences in either order.
- neighborhood_cross_cost_sum gives
  sum_{v in B} crossCost(B,N(v) intersect D)=sum_{z in D} deg_B(z)^2.
  These are the graph-level first/second moments used in Case 2, not merely
  algebra in abstract scalar variables.

WeightedProfile.lean (2 public theorems)
- weighted_profile_is_fractional_half: with E subset D, B disjoint D,
  |B|+|E|<=t<=|B|+|D|, |E|<|D|, and 2t=|V|, the profile
  1_B+1_E+w*1_(D\E), w=(t-|B|-|E|)/(|D|-|E|), lies in [0,1] and has mass |V|/2.
  The strict denominator hypothesis is explicit; no division-by-zero escape.
- weighted_profile_cost gives the exact edge-cost decomposition when E is
  independent. It identifies every actual graph cross term and internal term.

ProfileBound.lean (2 public theorems)
- mantel_induced derives e_G(F)<=|F|^2/4 from mathlib's proved Turan theorem
  on the actual induced graph; no external Mantel theorem is assumed.
- weighted_profile_cost_bound applies the incidence bounds and Mantel to
  every Case 2 profile. With w>=0, E subset D, E independent and
  deg_B(u)<=|B|/2 on D, its cost is bounded by
  e(B)+sum_E deg_B + w*|D\E|*|B|/2 + w*|D\E|*|E| + w^2*|D\E|^2/4.
  Together with w*|D\E|=t-|B|-|E| this is the paper's unnormalized bound.

REMAINING DEPENDENCIES, NOT HIDDEN AS AXIOMS
1. Assemble maximum-independent-set selection, greedy output and the D
   construction into the paper's complete branch split, including exact
   even-cardinality/parity bookkeeping. The components exist; their universal
   composition does not yet.
2. Finish finite averaging/selection in Case 2. The first and second moments,
   feasible profiles and their cost bounds are checked. Still connect the
   degree interval, the second-moment bound, Jensen/variance for the concave
   quadratic, and existence of a vertex with cost at most the average.
3. Connect normalized b,d,h,k,r values and the piecewise scalar envelope f.
   Do not mistake separate scalar certifications for this graph theorem.
4. Use an explicit BCLCutCertificate input for the max-cut theorem (or prove
   the external theorem); combine the two graph constructions with the
   already checked scalar envelope, then use existing fractional rounding.
5. Handle odd order / blow-up reduction and the n=0 boundary in a top-level
   statement. Our exact-half construction appropriately requires 2t=n.
No BCL, completion, normalization, averaging, or blow-up axiom was introduced.

DIAGNOSTICS / ATTEMPTED FALSIFICATION
Run python3 diagnostic.py. This checks 388 labeled triangle-free graphs on
five vertices: 67,017 valid independent-extension identities and 12,416
heavy-neighbor independent sets. These finite checks diagnose conventions;
the general conclusions come from Lean, not finite enumeration.
A genuine stopped Case 1 is exhibited in the Petersen graph KG(5,2): n=10,
maximum independent A=B has size 4, outside degree into B is 2>k*n=1,
C is empty, choose D of size 2, m=1 and a neighbor E of size 1. The selected
half has exactly 2 edges, matching e(B)+m*|B|/2. The JSON records all edges
and labels. Negative controls fail if triangle-freeness or disjointness is
removed, confirming that the tested assumptions do real work.

One repairable display error in the newer paper was found: the unqualified
identity f(alpha)-alpha*(1/2-alpha)/2=2*(alpha-3/8)^2 only holds on the first
branch [1/3,3/8]. At alpha=2/5 the left side is 0 and the right side is 1/800.
For alpha>=3/8 the left side is 0. The inequality actually used by the proof
still holds; this is not a counterexample to the claimed extremal bound.
No other counterexample was found in this bounded semantic inspection.

PROVENANCE / NOVELTY
The graph definitions and ordered-sum helper proofs are from aimir's baseline,
not invented here. CompletionBranch's private helpers are adapted from
LowDensityConstruction.lean at the exact baseline commit below. Other new
components formalize the newer note's construction, largely attributed there
to Razborov Section 4.5. We claim a checked implementation of these components,
not new graph theory or priority. Upstream source/licensing provenance must
remain attached if this scratch code is later prepared for distribution.

Baseline graph repository, inspected pinned source (no upstream edit):
https://github.com/aimir/erdos-128-sparse-halves/tree/ba85f319ebb33ec2194ef4c2929a12916329e1e7
Exact source of borrowed helper proofs:
https://github.com/aimir/erdos-128-sparse-halves/blob/ba85f319ebb33ec2194ef4c2929a12916329e1e7/lean/Erdos128/LowDensityConstruction.lean
Newer construction source, inspected pinned source:
https://github.com/pma1999/erdos-128-sparse-halves/blob/2193a4a06a4ec288a53ae986cdca5c1082abf1bb/outputs/cut-independent.tex
Mathlib checked Mantel/Turan source:
https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean

REPLAY
Run python3 verify.py. It copies all seven local modules into a fresh directory,
compiles them using Lean 4.35.0 and the pinned cached mathlib packages, audits
all sixteen new theorem closures, then runs leanchecker on those local
modules. No original controls or prior bridge .olean is used. Mathlib and its
package artifacts remain cached trusted dependencies, clearly disclosed.
The prior DeletionBridge source and verification artifacts are not modified.
Fresh module replay is kernel checking into imported environments, not a
second independent theorem prover and not a fresh rebuild of all mathlib.
Exact hashes, exit codes, durations and paths are in completion-verification.json.
