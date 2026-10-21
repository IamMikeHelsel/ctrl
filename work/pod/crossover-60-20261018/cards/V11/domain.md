# V11 domain research: admission, information algebra, and actual error

AI-written by domain role; inherited root model, exact identifier unavailable. Work isolated
under this card. PM owns elapsed timer, final grade and decision.

## Source recovery and binding

Original question: can geometric outlier rejection preserve a stated estimation-error bound
when composed with an additive information update? The source survey suggests this transfer;
its concrete InformationFilter.lean proves two-sided inverse identities in an arbitrary
associative ring. The theorem assumptions are inverse witnesses and algebraic definitions.
They do not include a true state, observation model, mean update, random variables, covariance
positivity, independent noise, admission predicate, or deterministic error radius.

The imported ScalarKalman.lean defines postVar as (1-k)^2 P+k^2 R and proves optimization and
precision identities for that expression. It does not formalize the statistical assumptions
which make this expression an actual covariance. The prose's statistical interpretation needs
those assumptions separately. Nothing in the experiments refutes either algebraic identity.
The scalar information mean introduced below is an explicit added model, not an already proved
source theorem. Source U,V ring elements are general; the final C_mat specialization uses the
same element on both sides and does not itself supply transpose/rectangular-matrix typing.

## Exact sharp deterministic gate

Fix one scalar state x, prior mean mu and certified radius a>=0. A measurement z has a
SEPARATELY SOUND hard error bound b: |x-z|<=b. This is stronger than geometric compatibility
and cannot be obtained merely by observing that two intervals intersect.

With positive algebraic covariance weights P,R, information mean
c=(mu/P+z/R)/(1/P+1/R)=mu+[P/(P+R)](z-mu), and information covariance PR/(P+R).
The true state belongs to [L,U], where L=max(mu-a,z-b), U=min(mu+a,z+b).
For L<=U, the exact gate guaranteeing |x-c|<=E for EVERY feasible x is

    c-E <= L  AND  U <= c+E.

Necessity follows by testing both endpoints; sufficiency follows by interval containment.
Its sharp radius is max(|L-c|,|U-c|). Empty intersections are rejected explicitly so that
vacuous universal assertions cannot appear as safe estimates. The sound measurement premise
is essential even if the endpoint gate passes. This can be used beside additive information
bookkeeping without interpreting the latter as a deterministic certificate.

If only the prior is certified, the sharp worst-case bound after any displacement d is

    sup_{|x-mu|<=a}|x-(mu+d)| = a+|d|.

Therefore preserving the SAME prior hard radius for all possible actual truths requires d=0.
A residual-only geometric gate cannot universally justify a nonzero correction against
arbitrary admitted outliers. This is a precise limitation, not a claim that useful inlier
certificates or probabilistic gates are impossible.

## Positive and negative exact tests

1. Compatible outlier: mu=0,a=1,x=-1,z=21/20,b=1/10,P=1,R=1/100. Residual compatibility
   holds; mean=105/101, covariance=1/101, actual error=206/101>1. The actual sensor bound
   is FALSE. This demonstrates the missing truth-containment assumption, not a failure
   of the conditional interval theorem.
2. Valid bounds but false covariance-radius claim: mu=0,a=1,x=3/5,z=1/2,b=1/10 with the
   same P,R. Both hard bounds hold. Mean=50/101; actual error=53/505, whose square exceeds
   covariance1/101. Feasible interval[2/5,3/5] has sharp radius53/505 about this mean.
   Radius1/10 is rejected; radius53/505 is accepted and kernel-certified sharp.
3. Zero innovation: mu=z=0,x=1,a=1,b=1/10. Mean does not move, but contraction to the
   purported sensor interval still excludes truth because the sensor bound is false.
4. Empty intersection rejects. An exact sensor fixture with b=0 verifies the nonempty
   singleton limit, retaining the information mean and its nonzero residual distance.

`domain_exact.py` uses Fraction arithmetic for six fixtures and 4,284 finite endpoint-gate
comparisons. This finite enumeration is diagnostic evidence, not the universal proof.
`domain_gate.lean` proves eight lemmas: interval iff, actual-bound intersection, prior-only
iff, zero-displacement consequence, information mean identity, two counterexamples, and
sharp positive repair. It compiled under ctrl pinned Lean4.33.1 with only propext,
Classical.choice, Quot.sound. The initial additive-order tactic failure is retained in
`domain_gate_failed_attempt_1.log`; it is not promoted. File frozen for independent replay.

## Selection changes covariance even without biased input errors

An additional exact four-world fixture fixes independent equiprobable prior error e and
measurement noise v in {-1,+1}; each Cartesian product pair has probability1/4. Take P=R=1,
true state0, mu=e,z=v, gain1/2. The posterior error is(e+v)/2, with unconditional mean0 and
variance1/2, exactly the source formula. Admit only innovation z-mu=v-e=0. This leaves the
two equal-sign worlds, each with conditional probability1/2. Conditional mean remains0,
but variance is1 and conditional E[e*v]=1, despite the original independent errors.

This shows the cross term discarded in the usual unconditional covariance derivation can
reappear after data-dependent admission. `domain_selection.py` checks all rational moments
and saves the explicit worlds. The separate Lean arithmetic certificate verifies the
cross-term identity and enumerated moments; it is not a general probability-space theorem.
No extrapolation to jointly Gaussian independent errors is claimed: that case has additional
structure and must be assessed separately. The zero threshold is an intentionally simple
finite-law counterexample; any threshold between0 and2 has the same accepted worlds here.

## Scope, gate, next test, and verification

Recommend GO for a conditional proof-carrying admission interface: retain information algebra
and require an independently justified truth-containing observation set, then check its
posterior containment before announcing a deterministic radius. HOLD for a physical/geometric
implementation until a concrete observation model, calibration/error envelope, association
assumption and geometric certificate implying actual truth containment are supplied.
Reject the shortcut from low geometric residual or decreasing covariance to an actual bound.

Next discriminating test: bind one real geometric observation model to a truth-containing set
including calibration and association alternatives. Test both a valid certificate and an
alternative-pose/outlier witness that passes residual checks. Avoid silently replacing a
multimodal pose set by a single locally linearized Gaussian.

Reproduction:

    uv run python work/pod/crossover-60-20261018/cards/V11/domain_exact.py
    uv run python work/pod/crossover-60-20261018/cards/V11/domain_selection.py
    cd lean
    lake env lean ../work/pod/crossover-60-20261018/cards/V11/domain_gate.lean
    lake env lean ../work/pod/crossover-60-20261018/cards/V11/domain_selection.lean

No original source edited, no numerical solver output used as proof, no robot validation.
Scoped Python ruff passed. Repository-wide integration checks are PM-owned because this worker
made only isolated research artifacts. Independent critic replay requested after freezing.
Quality estimate: faithfulness4,reproducibility4,discrimination4,critique4,actionability3 =19/20
(95%) for the scalar obstruction/interface; subjective confidence high in exact scalar claims,
limited on practical geometric admission until the named missing assumptions are supplied.

## Positive geometric bridge supplied by the inventor and checked by domain

A concrete 2D linear fixture closes the scalar gate's missing implication within an explicit
redundancy assumption. Observe rows H(x,y)=(x,y,x+y,x+2y), z=(1,0,0,0). Assume at most one
row has error larger than epsilon, with 0<=epsilon<1/4. Quantify the union of ALL four
three-inlier branches. Each branch containing row1 implies either1<=3epsilon or1<=4epsilon
and is impossible. The remaining branch234 implies |y|<=epsilon and |x|<=2epsilon.
This is a truth-set argument, not selecting a low-residual fit and declaring it correct.
The world(2epsilon,-epsilon) attains the x bound. At epsilon=1/4 the additional world
(3/4,-1/4), compatible with rows124, violates |x|<=2epsilon: the strict threshold is sharp.

`domain_geometry.lean` formalizes the union-of-branches implication, attaining witness,
and threshold failure. The first attempt lacked the ring tactic import and is preserved
as a failed compile log; no failed lemma is counted as proved. The original source is
unchanged. This is a synthetic linear geometric example; a camera projection/pose problem
still needs its own observation model and observability/association assumptions.

With prior mean0, the certified surviving measurement values are all0, so an information
mean update on rows234 stays0. For unit prior information and unit measurement weights,
the information matrix is [[3,3],[3,7]], inverse(1/12)[[7,-3],[-3,3]]. These algebraic weights
remain distinct from the deterministic coordinate error certificate. The geometry supplies
a real sufficient inlier implication under the explicit max-one-corruption model.

Independent critic reconstructed the scalar gates and four-world moments without importing
producer experiments; eight gate lemmas passed independent kernel/axiom replay. Three
selection arithmetic lemmas also passed producer compilation with allowed axioms; critic
replay is underway. Python files were formatted only after the critic confirmed independent
reconstruction, then scoped ruff check and format checks passed.

The geometry file's final compile succeeded for all three declarations with the permitted
axioms. The phase threshold is universal in epsilon, not a finite sampling result. A separate
`domain_survivor.lean` adds the measurement-level interface: under the same complete branch
assumption and strict threshold it returns all three actual surviving observation bounds,
rather than asking a consumer to reconstruct those from the state bounding box.

Final boundary: the four domain Lean files prove mathematical implications from the explicitly
complete four-branch disjunction. They do not validate serialized branch IDs, runtime manifest
completeness, or provenance of an adapter's claimed information rows. They import no inventor
Python adapter or serialized certificate. A certificate-to-branch binding failure invalidates
that adapter's acceptance, without invalidating the conditional mathematical theorem. Runtime
admission must still reconstruct/check the full branch model and bind certificates to it.
The final survivor lemma compiled with allowed axioms, bringing the producer total to15.
