# V06: Pose-graph synchronization certificates

**PM: GO for a model-bound exact certificate consumer.** AI-written wildcard review by root PM, domain researcher, inventor and independent critic. Inherited root models; exact runtime identities unavailable, no claim of model-family diversity. Actual timestamps and substantive elapsed time are in campaign state/activity.

Frozen question: Can a small inconsistent relative-pose graph be accompanied by an independently checked certificate of global optimum after gauge fixing?

Yes, for the explicit fixtures below. The source was only a catalogue entry in .agents/teamwork/explorer_survey_vision_1/handoff.md. No local SE-Sync implementation had been inspected. We checked the primary SE-Sync report and author correction; this review does not claim a new synchronization algorithm or absence of prior formal work.

Primary sources: [SE-Sync extended report](https://arxiv.org/html/1612.07386), [author corrigendum](https://david-m-rosen.github.io/files/SESync_correction.pdf). The established mechanism is a feasible pose attaining a verified relaxation lower bound. Tightness is conditional or verified for an instance; SO versus O feasibility, gauges and disconnected components remain distinct. The correction repairs a KKT proof error in Theorem12 while preserving its statement. Our concrete square certificates avoid that erroneous argument. The report's directed noise convention matters for the translation reversal test below. More source context is in pm_primary_sources.md.

## Original obstacle and three transfers

1. Cycle holonomy and gauge theory: compose relative rotations around a cycle to expose inconsistency, then anchor a node. This preserves frame-change symmetry but neither fixes a global optimizer nor proves uniqueness. Changing weights while retaining the same holonomy changes both.
2. Passivity/positive energy and proof-carrying optimization: replace trust in optimizer convergence by exact nonnegative quadratic energy, a feasible pose and a matching lower bound. Rational LDL or a sum-of-squares factor is independently checkable. It fails if the graph/objective binding, SO membership or exact PSD premise is missing.
3. Unexpected spin frustration and polygon closure: an all-half-turn triangle becomes a weighted vector-closure problem. Depending on weights, the same cycle inconsistency permits two chiral optima or one collinear optimum. Slack nullity alone cannot classify the nonlinear feasible intersection. This gives useful equality/uniqueness tests rather than treating all frustration as irrecoverable error.

## Exact fixtures and decisive results

**Unweighted half-turn triangle.** Directed edges01 and12 measureI; edge02 measures−I in SO2; all weights1, R0=I. Actual Frobenius objective satisfies

F=6+||R0−R1+R2||F².

Rotations(+60°, +120°) and(−60°,−120°) both attain6 and are distinct after the gauge is fixed. Rational dual slack is the outer product of(1,−1,1), tensored withI2. A kernel-checked parameterization lemma covers every proper orthogonal2×2 matrix, so this is a global matrix-objective bound. All-identity is stationary yet costs8; an exact negative slack direction rejects its global certificate.

**Rational interior triangle.** R1 has(cos,sin)=(4/5,3/5); R2=(7/25,24/25). Measurements01=12=I,02=(-44/125,117/125), unit weights. The cycle is inconsistent. Objective12/5 equals the dual bound with node multipliers2/5. Root constructs an exact rational slack factorization with pivots(8/5,8/5,39/40,39/40,0,0), rank4, and exact complementary slackness. An independent critic rebuilds the Laplacian from separately declared directed measurements and checks every rational equality. Root's explicit four-square identity proves the global bound and unique anchored optimum in Lean. Matrix-objective bridge acceptance is recorded in the final replay manifest.

This extends to a concrete FULL SE2 problem with nonzero translations: p0=(0,0),p1=(1,0),p2=(1,1); measured translations01=(1,0),12=(3/5,4/5),02=(1,1); translation weights1. The candidate has zero translation residual. Every competitor has nonnegative translation cost, so the rotational lower bound12/5 remains valid. Root's full-objective theorem proves attaining candidate and anchored uniqueness; domain matrix/vector bridges bind arbitrary proper rotations and actual directed residuals. This is one explicit pose graph, not a generic translation-elimination compiler or SE3 result.

**Weighted frustration.** All measured rotations−I, weights(15,12,20). With a=(5,3,4), F=88+||5R0+3R1+4R2||F². Rational candidates R1=(-3/5,4/5),R2=(-4/5,-3/5), and their conjugates, attain88. Changing only weight12 to13 preserves holonomy but makes the old pose cost92; an exact rational perturbation improves it by728/10001. An old certificate must reject the changed objective.

For amplitudes(8,3,4), weights(24,12,32), a different PSD factor proves a unique anchored optimum96 at R1=R2=−I. At the boundary amplitudes(7,3,4), weights(21,12,28), the slack has larger nullity, yet the same feasible optimum is still unique: equality requires3(cosθ1+1)+4(cosθ2+1)=0, forcing both cosines−1. Extra slack nullity therefore does not itself prove multiple optimal poses. Boundary kernel acceptance is recorded separately; exact independent rational/equality checks also pass.

**Locally good wrong branch.** A separate triangle uses candidate(cosθ,sinθ)=(5/13,12/13), R1=Rθ,R2=R2θ and measurement02=R3θ. Exact cost is96/13. The angle-gradient cancels and the local Hessian is positive, but the candidate dual slack has an explicit negative direction−69/130. A rational competing pose has cost258992/54925, improving by146608/54925. The local-Hessian calculus bridge is hand-derived; exact objective and quadratic-form comparisons are independently checked. Local stationarity and curvature cannot replace global certification.

## Independent critique and acceptance failures

The critic's separately implemented consumer accepts the rational positive and rejects20 mutations involving SO membership, anchor, graph data, edge direction, weights, objective, factor, slack, multiplier and rank. A correct inverse-edge change passes for the ROTATION-ONLY objective. A tiny negative diagonal entry−10^-12 defeats a numerical PSD tolerance of−10^-9; exact factor checking rejects it.

For full SE2, inverse group reversal is different: replacing(M,t) with(Mᵀ,−Mᵀt) and reversing the directed residual changes the formerly zero translation cost to8/5 in this inconsistent-rotation fixture. Total cost becomes4. The directed statistical model must therefore be bound, not silently normalized as an undirected equivalent. Mutating one measured translation by.01 gives the old candidate an extra1/10000; this rejects old tightness without asserting the new optimum.

A fixed-three-node inventor prototype accepts an unused fourth pose. The objective bound survives, but an isolated component has an independent gauge and destroys global uniqueness under a single anchor. This is a preserved interface gap, not a hardened production consumer. The next implementation must bind node count, graph universe and componentwise gauges as well as the equations.

## Evidence and decision

Kernel artifacts cover concrete objective identities, global lower bounds, feasible attaining poses and selected uniqueness statements; only propext,Classical.choice,Quot.sound are permitted. Exact replay counts, hashes and failure logs are retained. One full-SE2 proof attempt exhausted the default200000-heartbeat tactic budget; replacing unnecessary nonlinear proof search by linear reasoning preserved the statements and passed. Failed logs are not accepted proofs. Generic graph compilation, certificate-parser correctness and a production SE-Sync integration are not verified here.

GO after all60 initial sessions: one30-minute block on a reusable manifest-bound consumer across20 declared held-out SO2/SE2 fixtures, including changed weights, directed translations, disconnected components, reflections, rank-boundary uniqueness, wrong stationary branches and near-PSD slack. Bind exact objective, full node set and gauge; emit separate optimality, uniqueness and bounded-gap results. Require independent replays and kernel checking of promoted certificates. No broad tightness, SE3, novelty or physical localization claim.

Quality rubric: faithfulness4,reproducibility4,discrimination4,independent critique4,actionability3 = **95/100**. Review quality is not a probability of scientific success. Subjective confidence is high in the scoped exact fixtures; generic and physical transfer remain open.

Final acceptance:41 declarations independently replay with permitted axioms, including actual matrix/vector fullSE2 global optimum and uniqueness. Current source hashes match all accepted records in pm_final_acceptance.json; generic compiler/manifest correctness remains outside those theorems.
