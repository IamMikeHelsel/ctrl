# V06 cross-discipline inventor

An inconsistent weighted SO(2) triangle admits an exact rational global certificate. It also demonstrates why gauge fixing and cycle consistency do not establish uniqueness or certify a weighted optimum. The useful next step is a small certificate consumer that binds every weight, directed measurement, dimension, orientation constraint and objective normalization before checking a positive slack factor and primal-dual equality.

Model: inherited root model, exact identifier unavailable. AI-generated research. The frozen local source is a survey entry, not an inspected local SE-Sync implementation. This review did not run SE-Sync or claim a new optimization method.

## Primary source boundary

[SE-Sync](https://arxiv.org/abs/1612.07386) describes a relaxation that is exact under a suitable noise regime and can certify exactness afterward; this is not unconditional tightness for arbitrary corrupted data. The [authors' corrigendum](https://david-m-rosen.github.io/files/SESync_correction.pdf) repairs the proof of Theorem12 while retaining the theorem. Its original intermediate KKT point minimized an expression that needed maximizing; active inequality boundaries had been omitted. The corrected argument uses the singular-value upper bound coming from orthogonal blocks. Our exact certificates below do not invoke that theorem, its noise threshold, or any novelty assertion from the local survey.

## Three transfers

1. **Cycle holonomy as a consistency syndrome.** Directed edge rotations compose around a cycle; reversing an edge requires its transpose. The product detects whether zero residual is possible for a connected rotation-only graph. It preserves the group-valued cycle defect, not the confidence weights or the optimum's allocation of residual. Falsifier: changing only one edge weight below preserves the same −I cycle holonomy but makes the previously certified optimum suboptimal. Local-frame changes produce non-self-transpose measurements so a consumer cannot accidentally pass direction tests only because the base measurements are symmetric.

2. **Electrical-network energy and passivity-style factorization.** Assemble the exact block connection Laplacian L from the actual weighted residual objective. A block-diagonal dual Λ with `L−Λ=CᵀC` gives a nonnegative excess energy for every feasible rotation assignment; a feasible candidate attaining the dual value is globally optimal. This is an algebraic energy certificate, not a dynamical stability claim. Preserve the objective's Frobenius normalization and directed-edge multiplicity. Falsifiers: unchanged factor with a changed weight; a stationary candidate with nonzero primal-dual gap; or accepting O(2) membership where SO(2) was requested.

3. **Unexpected frustrated-spin/polygon closure.** When all three measurements are −I and edge weights are `a_i a_j`, the optimization becomes closure of three weighted planar unit vectors. This is useful for inverse-designing exact, adversarial certificate fixtures with known optima. Interior triangle lengths give chiral alternatives; a dominant length gives a collinear minimum. The same graph and holonomy can therefore have two distinct gauge-fixed optima or one unique optimum. It preserves the special rank-one weight structure and SO(2) geometry; generic pose graphs and SO(3) do not inherit the formula. Falsifier: a1=8 exceeds a2+a3=7, so the old zero-closure lower bound cannot be attained, even though it remains a valid bound.

## Exact weighted certificate and semantic negative controls

Use directed edges (0,1),(1,2),(0,2), each once, and

`F(R)=Σ w_ij ||R_j−R_i M_ij||_F²`, `R_i∈SO(2)`, `R_0=I`.

All M_ij=−I, weights are15,12,20, and a=(5,3,4). Define R(c,s)=[[c,−s],[s,c]]. The rational candidate is

`R0=I`, `R1=R(−3/5,4/5)`, `R2=R(−4/5,−3/5)`.

Then `5R0+3R1+4R2=0` and, for every feasible assignment,

`F=88+||5R0+3R1+4R2||_F² ≥88`.

Equivalently Λ has scalar blocks(10,18,16), and slack `(aaᵀ)⊗I` has the explicit rational two-row factor stored in `inventor_cycle.json`. The candidate and its entrywise conjugate/transposed rotations are distinct optima with the same fixed R0. This already disproves “fixing the gauge makes the minimizer unique.” The independent Python consumer reconstructs L from the passed graph, checks gauge and SO(2), exact factorization and the primal-dual gap.

Concrete mutations all execute:

* Weight12→13 gives the old candidate cost92. Rotate R1 by the rational half-angle parameter −1/100; the feasible new candidate lowers cost by728/10001. The old factor fails graph binding.
* At all-identity rotations the gradient is zero because every edge residual angle isπ, but cost376 exceeds88. The global consumer rejects its primal-dual gap.
* Apply local frame changes Q0=I,Q1=R(5/13,12/13),Q2=R(3/5,4/5), with `R_i'=R_iQ_i` and `M_ij'=Q_iᵀM_ijQ_j`. The transformed candidate and factor pass. Reversing every edge **with** transpose passes; reversing without transpose fails exact graph/slack binding.
* A reflected candidate fails SO(2) membership. Our bound also holds over the broader O(2) feasible set, but this does not permit reporting an improper candidate as the requested SO(2) solution.

The factor check and gap are complementary. A valid lower bound does not certify a candidate until equality and feasibility are checked. No floating eigensolver or solver success flag is used.

## Same holonomy, unique optimum

For a=(8,3,4), weights become24,12,32. The generic closure lower bound is94, but |8z0+3z1+4z2|≥1 for unit vectors, so94 cannot be attained. The candidate R0=I,R1=R2=−I has cost96. An exact stronger slack certificate is

`S=(8/7)(7,3,4)(7,3,4)ᵀ+(12/7)(0,1,−1)(0,1,−1)ᵀ`.

It equals `[[56,24,32],[24,12,12],[32,12,20]]`, with Λ=(0,24,24). Thus

`F=96+(8/7)||7R0+3R1+4R2||_F²+(12/7)||R1−R2||_F²`.

Both coefficients are positive. Equality forces R1=R2 and7R0+7R1=0, hence R1=R2=−I after the gauge is fixed. This gives uniqueness by equality conditions, not by merely citing graph connectivity. The scalar slack has a nonzero rank2 minor96 and nullspace spanned by(1,−1,−1). `inventor_phase.py/json` independently verify the rational factor and candidate cost.

At the boundary a=(7,3,4), the scalar slack has rank1 again, but the optimum is still unique after fixing R0: equality gives `7+3cosθ1+4cosθ2=0`; since each cosine is at least−1, both must equal−1. This exact boundary diagnostic is recorded in `inventor_phase.json`. Extra slack nullity alone therefore does not establish multiple feasible optima; the intersection of its equality space with the rotation constraints matters. This boundary reasoning is analytic, not one of the nine compiled lemmas.

Subsequent initial-session supplement: the boundary reasoning is now separately kernel-checked in `inventor_boundary.lean`. Five additional lemmas prove its explicit objective identity, global lower bound96, feasible candidate, unique circle-coordinate minimizer and rank-one quadratic-form identity. The log shows only propext/Classical.choice/Quot.sound. The earlier nine-lemma file was left unchanged. The general graph-to-matrix compiler limitation below still applies.

## Scope, evidence and next action

This solves a declared small **rotation-only SO(2)** instance. It can be embedded in a deliberately chosen SE(2) case with all measured translations zero: the translation objective is nonnegative and is attained at all t_i=0; positive connected translation weights and t0=0 then fix translations. That is a stated special case, not a general translation-elimination proof or a 3D pose-graph certificate. In SO(3), −I is improper, so directly transplanting these measurements is invalid.

Python exact rational certificates and negative controls pass; scoped Ruff passes. Nine lemmas in `inventor_weighted.lean` compile using only propext/Classical.choice/Quot.sound. They prove the explicit circle-coordinate objectives' SOS identities, global bounds, candidates, feasible weight-mutation improvement, and unique optimum for the dominant-weight case. This formalization does not yet prove a generic matrix-to-scalar graph compiler correct. The generic consumer itself has not been verified in Lean. No robot validation, probabilistic accuracy guarantee, or claim of underlying true-pose recovery follows from globally minimizing this objective.

An additional changed-graph negative adds an isolated fourth node: arbitrary proper R3 leaves objective88 unchanged while R0 remains fixed. `inventor_disconnected.json` records this test. The small Python prototype also accepts the extra unused pose because it has no independently supplied frozen nodecount/manifest. It must not be promoted as a production acceptance interface. Global optimality of the objective on the used nodes remains true, but uniqueness and statement binding to an intended graph require separate checks. This limitation is preserved rather than hidden by silently changing the interface.

GO for a30-minute acceptance adapter: bind a frozen graph manifest to rational primal/dual certificates; verify the universal objective identity in Lean; preserve frame-reversal, weight, gap, orientation, disconnected-component and false-uniqueness mutations. HOLD general SO(3)/SE(3) or arbitrary noise until the model and certificate support them. NO-GO for holonomy alone, stationarity alone, or numerical PSD assertions as global certificates.

Rubric: provenance4/4, transfer diversity4/4, falsifiability4/4, exact tests3/4, scope4/4=19/20 for this scoped inventor exercise; subjective confidence97% in the checked rational identities, lower for an unimplemented general adapter. Novelty unassessed.
