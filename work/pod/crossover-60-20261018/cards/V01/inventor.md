# V01 inventor: preserve the geometry and carry its visibility contract

AI-written contribution; inherited root model, exact identifier unavailable.
Read the actual `ControlsLean/Vision/Homography.lean` and its proposal. The source proves
matrix identities over any field. Its plane theorem requires d≠0 and the plane/motion
equations; it does not require R∈SO(3), nonzero target depth, nonzero rays, or positivity.
The projective incidence theorem separately assumes an inverse. These are useful and
correct algebraic scopes. The proposal's stronger visibility and uniqueness language is
not inherited automatically. In particular, epipolar identity validity does not cease
on a plane; identifiability is a separate question already examined in V03.

## Three transfers and discriminating tests

**1. Dual variables from mechanics: transport the covector, not just the point.**
Point-line pairing plays the same algebraic role as force–displacement or dual–primal
pairing: if points use H, covectors use H inverse-transpose. This transfers the invariant
pairing, not a Euclidean image distance or a physical force interpretation. An explicit
all-visible plane example uses R=I,t=e1,n=e3,d=1, giving H=I+e1e3ᵀ. The point p=(0,1,1)
lies on l=(1,0,0). Its transformed point is(1,1,1). The correct line(1,0,−1) has pairing0;
applying the point rule to the line instead gives(1,0,0), pairing1. This is a concrete
consumer mutation with proper R, invertible H, and positive depths on both sides.
Falsifier: use the point transform for both objects, or interpret the preserved homogeneous
pairing as a scale-independent pixel distance. No new incidence theorem is claimed here;
the useful next step is a consumer that checks the line's inverse and its representation.

**2. Hybrid systems and partial charts: separate a coordinate singularity from a lost ray.**
A proper quarter-turn about y sends(u,v,1) to(1,v,−u). With t=0 and plane Z=1 this is
exactly the source plane homography, with determinant1. At u=0 the ray is nonzero but
the usual target z=1 chart is unavailable. Dividing by its first coordinate remains
algebraically valid, giving(1,v,−u). A chart switch therefore preserves the projective
object but does not make it visible in the original pinhole image: target depth is−u,
so visibility requires u<0, and u=0 is the image horizon. A hybrid chart dispatcher needs
both a nonzero-chart guard and the physical camera visibility guard.

The same fixture provides a quantitative falsifier: u=−1/n and u'=−2/n give first-pixel
sensitivity ratio n²/2, despite strictly positive depths and a fixed invertible proper
rotation. Thus nonzero depth alone gives no uniform error bound. A declared margin
u,u'≤−δ<0 supplies

|1/u−1/u'|≤|u−u'|/δ²,

and, for |v'|≤B,

|v/u−v'/u'|≤|v−v'|/δ+B|u−u'|/δ².

The derivation is elementary fraction subtraction and denominator bounds. Exact rational
probes check it; they are not the proof of the universal inequality. A margin enables
interval propagation and chart admission; it does not preserve conditioning uniformly as
δ→0. The root owns a complementary finite-patch quantitative certificate.

**3. Unexpected transfer: oriented rays and passive-frame payloads.**
The quotient by all nonzero scales forgets orientation; a physical forward ray uses
positive scales. The proper half-turn R=diag(−1,1,−1) sends(.5,0,1) to(−.5,0,−1).
Normalized pixels are identical, the source plane equation holds with plane Z=1,t=0,
and H is invertible, yet the target depth is−1. This does not refute the source identity;
it refutes inferring visibility from an unoriented projective correspondence.

There is a separate estimated-matrix gauge issue. If Hhat=αHphysical, then pixels agree
for every nonzeroα, but the physical depth ratio is (Hhat p)_z/α. The raw height of Hhat p
is therefore a visibility test only in the canonical physical gauge or with known signα.
For the quarter-turn and p=(−.2,0,1), physical target depth is+.2, whereas α=−3 gives
estimated height−.6 and identical pixels. Using absolute height can support a projectively
scaled residual bound, but cannot by itself establish oriented visibility. This negative
changes only the matrix representative, not the physical camera pose.

The quarter-turn example also transports the source guard−u−.1≥0 by its line covector.
Homogeneous pairings are exactly equal. For u=.1, however, normalizing the negative-depth
target ray changes a negative pairing into a positive one. Therefore incidence equality
survives arbitrary nonzero scaling, while a halfspace inequality requires positive scaling
or explicit orientation bookkeeping. This is an exact false-admission negative, not a
claim about an existing vision safety controller.

The line covector itself also needs an orientation convention for inequalities: l and−l
define the same projective zero-set but opposite halfspaces. An estimated H gauge scales
its inverse-transpose line by1/α. Positive physical ray depth alone does not fix an
unbound line sign. Absolute residual certificates avoid this sign ambiguity; signed
admission predicates must bind both representatives.

A related positive transport is useful for passive changes of coordinate basis. For
orthogonal Q1,Q2, carry

R'=Q2 R Q1ᵀ, t'=Q2t, n'=Q1n, H'=Q2 H Q1ᵀ,

along with rays x1'=Q1x1,x2'=Q2x2. Distances d and ray multipliers d1,d2 are unchanged.
The plane/motion constraints follow directly by substitution. The optical-axis covector
must also move: a1'=Q1a1. The exact fixture R=I,t=(1,2,3),n=e3,d=2 and X=(2,1,2), with
Q1 a quarter-turn and Q2 a half-turn about y, produces X'=(2,1,−2). Its new third component
is−2, but its unchanged physical depth is a1'·X'=e1·X'=2. Forgetting to transport the plane
normal gives the wrong motion prediction(−1,−1,1), instead of(−3,3,−5).
The target optical axis is−e3, so its physical depth remains5 even though Y'_z=−5.
Rays x1'=X'/2 and x2'=Y'/5 satisfy their transported optical-axis normalizations and
the exact source relation5x2'=H'(2x1'); both physical depths are positive.

This is a passive basis change, not a claim that an actively rotated camera keeps every
point visible. If a changed camera's optical axis is defined anew as coordinate e3, its
visibility must be recomputed. Nor may arbitrary image GL(3) transformations be called
physical camera rotations. The source's arbitrary ray-vector representation supports the
passive calculation without silently renormalizing rays by a negative third component.

## Evidence, limits and next action

`inventor_oriented.py/json` contains exact rational matrices, depths, incidence negatives,
chart cases, sensitivity probes and passive-frame transport. Every purported physical R
is independently checked for RᵀR=I and determinant1. Both translated and pure-rotation
examples retain the declared plane model. The examples are known geometric mechanisms,
not novelty claims, pose-identification results, or physical robot experiments.

`inventor_oriented.lean` contains eight isolated rational fixture lemmas. It uses the
available ctrl Lean4.33.1 environment. The notebook is pinned to4.36.0-rc1; its executable
exists locally but the required Mathlib artifacts were reported unavailable. These isolated
checks must not be presented as a fresh replay of the notebook's pinned source. The domain
researcher owns that replay boundary and source-specific strengthened statements.

`inventor_visibility.lean` additionally proves a generic obstruction on the nonzero
optical-axis family z·e3: no predicate can be both invariant under z↦−z and exactly classify
z>0. Its second lemma recovers canonical height by dividing by a known nonzero matrix
gaugeα. Both pass the isolated4.33 kernel with standard axioms; frozen SHA256
3beb95980a157d5595f13e08dd4a26e4eef4ddc990924248718937fc8205f613.
This formalizes the information lost by an unoriented projective quotient without assuming
every source ray is normalized or introducing an unproved physical sensor model.

Final producer status: all eight rational fixture lemmas also pass with standard axioms,
frozen SHA25651fb359d1f90ed2393db5d85d667a35a1a9aa34617ac4d18181cdc2da4944387.
Two earlier matrix-reduction/type-mismatch attempts are preserved as
`inventor_oriented_attempt0/1.lean/log`; neither is accepted evidence. Independent replay
of the final eight and the generic visibility two was requested from the critic. The critic
has independently agreed with the exact rational data and the physical/gauge distinctions.

GO: build an isolated contract adapter carrying an invertible H/inverse, point versus line
roles, nonzero rays, explicit camera/optical-axis convention, and positive depth margins.
Test it against the exact wrong-line, negative-depth, horizon, forgotten-normal and
forgotten-optical-axis mutations before accepting any inequality or pixel error certificate.
HOLD: physical sensing errors and a deployed camera/controller interface are unspecified.
Quality18/20 (faithfulness4,reproducibility4,discrimination4,critique3,actionability3).
Subjective confidence98% in the exact fixtures; no physical or novelty confidence implied.
