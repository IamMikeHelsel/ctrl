# Scale-free outer cones for a declared rotation cell

AI-written; a hand norm/camera derivation with separately kernel-checked polynomial
and scalar helpers. Not a fully assembled matrix/projection theorem or global search.

Let measured pixel be u∈R², true camera vector v=R(X−C)=(p,z), z>0,
and ||p−uz||≤γz. Preserve the same physical point X and camera center C when moving
to a nominal rotation R0: v0=R0(X−C)=R0Rᵀv. If ||R0−R||op≤δ,
then ||v0−v||≤δ||v||. This relation fails when extrinsic t is held fixed instead
of C; the exact counterexample is in pm_cell.json and independent critic evidence.

Require γ,δ,U,M,K≥0. If ||u||≤U and K²≥1+(U+γ)², triangle inequality gives ||v||≤Kz.
Write k=δK<1. Then z0≥(1−k)z>0. For B_u=[I₂,−u],
||B_u||op=sqrt(1+||u||²)≤M. Thus

    ||B_u v0|| ≤ ||B_u v||+||B_u(v0−v)|| ≤ (γ+Mk)z
                ≤ ((γ+Mk)/(1−k)) z0.

No upper bound on X or depth is needed for this homogeneous estimate. The image norm
is Euclidean per view; γ is the maximum over views. This is an outer implication:
feasibility of enlarged nominal cones does not imply a true camera exists.

For the domain fixture C1=0,C2=(1,0,0), both nominal rotationsI,
u1=(0,0),u2=(-1,1/2), the exact fixed-camera minimum is1/4.
At targetγ=1/10 choose U=9/8, M=3/2, K=8/5. These simultaneously bound both views.
For each true rotation in the declared Cayley parameter cube [-1/100,1/100]^3,
N=(1−s)I+2ppᵀ+2[p]×, R=N/(1+s), s=||p||².
The polynomial identities imply proper orthogonality and

    ||R−I||F² = 8s/(1+s) ≤24/10003 <1/400.

Hence δ=1/20 is valid (operator norm≤Frobenius norm), k=2/25, and
γouter=11/46<1/4. If a true point satisfiedγ=1/10 for rotations in these cells,
the SAME finite point and SAME fixed centers would satisfy both nominal cones at
11/46, contradicting the fixed-camera lower bound. The entire specified product of
two rotation cells is therefore excluded under this derivation's model assumptions.

The eight root helper proofs establish scalar ratio transport, Cayley numerator
norm/dot/determinant identities, and the smaller cube. Three additional helpers
establish the larger cube and exact sufficient-bound cutoff δ<3/56. The full matrix
orthogonality follows by cyclic identities; its assembly and the operator norm/
projection transport are hand arguments, not claimed as kernel-complete here.
125 exact grid points independently check the implementation, not all real cells.
The generated cube is local, not a covering ofSO3; rotations at the Cayley singularity
need another chart. No global completeness or search termination claim follows.

Failure controls: B_u norm is3/2 foru2, not1; its maximum gain has an exact rational
squared-norm witness. A squared Frobenius quantity cannot be substituted for its norm.
Keepingt fixed instead ofC breaks ray transport. δ≥3/56 only means this particular
bound loses rejection power; it does not certify feasible geometry. Negative or zero
nominal depth cannot be admitted by squaring inequalities.

This follows the established fixed-rotation/rotation-search distinction in Hartley
andKahl's author-hosted paper; it is a concrete checkable route, not a new global
optimization-method claim. Their presentation uses angular errors; this fixture and
bound explicitly use Euclidean image-plane errors instead.
