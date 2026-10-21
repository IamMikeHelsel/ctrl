# R11 — preserve world gaze by transporting the full frame jet

AI-written inventor review. Inherited exact model identifier unavailable. Root owns the600-second clock and PM decision. Own artifacts are `inventor_frame_jets.py/json` and `inventor_transport.lean`; original sources were read only.

The useful extension is a frame-consistency contract, separate from the domain role's scalar actuator tube. A world gaze direction alone is insufficient input to a moving-frame executor: its derivative jet must be transported with the base angular velocity and higher derivatives. Even a passive coordinate relabel can create a spurious world command if retained derivative coordinates are not transformed with position.

## Source and intended boundary

Read the frozen R11 card and `/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/robot-motion/stabilization-research-addendum-2026-10-18.md` in full. It is explicitly preparatory, with proposed multirate/frame/authority experiments. Its prior scalar execution results do not supply a coupled optical-axis or gimbal theorem.

No bird mechanism, IMAX mechanism, aerial hardware result, or biological implementation is inferred. I did not expand the addendum's abstract-level literature review into a claim of chapter-level validation. The transfers below are engineering hypotheses with explicit algebraic tests.

## Transfer1: covariant differentiation / moving-frame feedforward

Let R(t) be a proper rotation mapping body coordinates to world coordinates, with `Rdot=R Omega`, where Omega is the skew matrix of body angular velocity. Let d(t) be the intended **unit** world optical direction, and `p=R^T d` its body coordinates. Define `c=R^T d_dot`, `e=R^T d_ddot`, and `f=R^T d_dddot`. Product differentiation gives

```
p_dot   = c − Omega p
p_ddot  = e − 2 Omega c + (Omega² − Omega_dot)p
p_dddot = f − 3 Omega e + 3(Omega²−Omega_dot)c
          + (2 Omega_dot Omega + Omega Omega_dot
             − Omega_ddot − Omega³)p.
```

The order of the matrix products matters. The invariant preserved is the world jet: substituting these expressions into the derivatives of `d=Rp` reconstructs the requested world derivatives. This is a representation identity, not yet a sampled controller or plant-tracking guarantee.

`inventor_frame_jets.py` uses exact Taylor coefficients of actual smooth rotation paths

`R(t)=exp(t Z)exp(t² X/2)` and `d(t)=exp(t Y)exp(2t Z)e1`,

where X,Y,Z are the coordinate-axis skew generators. At t=0 the body jets are

`p=(1,0,0)`, `p_dot=(0,1,−1)`, `p_ddot=(−2,0,0)`, `p_dddot=(0,−1,10)`.

The script reconstructs all four world jets by Leibniz, checks the unit-direction derivative identities through order3, and rejects an omitted noncommuting `2 Omega_dot Omega` term. No floating-point integration is used.

A simpler falsifier keeps world gaze fixed at e1 while the base rotates at unit speed about z. The required body jets are `(e1,−e2,−e1,e2)`. Transporting velocity but setting body-coordinate acceleration to zero gives spurious world acceleration e1. Smoothness in the wrong frame does not preserve the task.

For bounded inputs, this identity suggests sufficient **ray-coordinate** derivative budgets. If `||Omega||<=B1`, `||Omega_dot||<=B2`, `||Omega_ddot||<=B3`, and world derivative bounds are D1,D2,D3, then

- `||p_dot||<=D1+B1`;
- `||p_ddot||<=D2+2B1D1+B1²+B2`;
- `||p_dddot||<=D3+3B1D2+3(B1²+B2)D1+3B1B2+B3+B1³`.

These triangle-inequality budgets require the declared norms and ||p||=1 throughout the interval. They are conservative and are not joint acceleration, joint jerk, or torque bounds. A constant-rate yaw joint q=−t has q_ddot=q_dddot=0, while its body ray `Rz(−t)e1` has coordinate acceleration and jerk norm1. That exact metric mismatch is included as a negative control.

## Transfer2 (unexpected): coordinate changes as transactions over retained history

Borrow a transaction's requirement that all related state refer to the same version. For a **constant passive basis change** Q, use

`Rnew=Rold Q`, `pnew=Q^T pold`, `Omega_new=Q^T Omega_old Q`.

Every retained vector jet transforms by Q^T, not just its position entry. The world products remain unchanged. If a whole retained reference is represented by vector-valued coefficients/events, a constant linear coordinate change must apply to every active contribution needed to reconstruct that reference. Merely changing a frame identifier does not transport numerical values. Euler-angle triples are not automatically vectors to which this rule applies.

Exact falsifier: stationary world gaze and base angular velocity Z as above, then relabel the body basis by90degrees about z. Correctly transporting all jets preserves world velocity0. Transforming position but retaining the old velocity numbers produces world velocity(1,1,0). The problem is internally inconsistent coordinates, despite noiseless sensing and a perfectly valid rotation.

The invariant is the physical world jet, not a preferred coordinate representation. This example is a passive constant relabel, **not** a physical base jump or an arbitrary calibration revision. A time-dependent Q introduces additional derivatives; a calibration update correcting an erroneous physical estimate needs uncertainty reconciliation rather than assuming it is a harmless relabel. No atomic executor has been implemented here.

The actionable next test is to commit a world-frame reference, change only a passive coordinate basis, and require unchanged world position/velocity/acceleration/jerk after evaluation. Then mutate exactly one retained jet or active event's frame version. The consumer should reject the mixed snapshot, rather than convert an inconsistent result into a valid-looking command.

## Transfer3: relative-motion viability and shared authority budgets

Borrow reference-governor reasoning, but apply it to the required **relative** output rather than independent base and visual-loop limits. In the scalar yaw restriction, world angle is `theta=b+q`, so exact world tracking requires

`q_dot=g_dot−b_dot`, `q_ddot=g_ddot−b_ddot`, `q_dddot=g_dddot−b_dddot`.

For an assumed relative optical-axis speed cap3/2, a base rate+1 and world target rate−1 require relative rate−2 and make exact tracking impossible at that instant. Both individual rates satisfy a unit bound; checking them separately misses the conflict. Conversely, co-moving base and target rates+1 require relative rate0. The exact tests preserve both the infeasible and favorable cases.

A robust independent rate box `|g_dot|<=G`, `|b_dot|<=B` yields the sufficient worst-case budget G+B. If the task and base motion are known to be correlated, retain their joint relation: for example `g_dot=b_dot+delta`, `|delta|<=eta`, requires only eta. Replacing a joint relation by independent marginal bounds can reject a feasible task, but it must not be replaced in the other direction without evidence.

This is a necessary feasibility gate under the stated output-rate model, not an optimal policy or a full gimbal actuator model. Actual joint limits need the relevant Jacobian/inverse-kinematics domain, singularity handling, joint state, and torque/response model. When the gate fails, silently clipping the relative command changes world gaze; retaining the original task requires an explicit bounded error/deadline relaxation or rejection policy.

There is also a manifold boundary: averaging antipodal unit gaze targets e1 and−e1 yields the zero vector. Normalizing that Euclidean reference is undefined at the midpoint. Reusing a scalar/vector FIR generator on unit directions therefore needs a declared chart or manifold construction; normalization is not a free preservation of derivative bounds. The script checks this exact midpoint negative.

## Formal evidence and what remains outside it

`inventor_transport.lean` compiles five printed declarations, with only permitted standard axioms. Frozen SHA256:

`fadf0d88203ed1858578106727204ccc92c8659e157cf1edbc0e3a2b63145b66`.

The first three are universal noncommutative-ring identities reconstructing first, second and third transported jets. The fourth preserves a product under a constant inverse basis change. The fifth checks the scalar opposed-rate obstruction. These kernel results certify the algebraic identities; differentiability, Rdot=R Omega, correct identification of frame/body signals, and instantiation as physical actuator derivatives remain the explicit analytic/model bridge. No theorem claims a biological, IMAX, or physical robot result.

The exact Python script checks concrete3D paths and mutations. It passes Ruff check and format. The domain role's scalar held-command actuator calculation is complementary; this report does not claim the two have been integrated into a3D closed loop.

## PM recommendation

GO for a typed frame-jet transport adapter and a relative-authority admission gate before a3D execution claim. Keep physical multi-axis tracking HOLD until a measured/declared joint dynamics model, sensor/clock uncertainty, authority, calibration domain, and singularity policy are supplied.

The next bounded experiment should couple the domain's scalar held-actuator fixture to a declared yaw frame, retain its physical state, and submit the co-moving/opposed tasks with the same deadline. Require world-frame error reporting, explicit authority rejection, and invariance under a constant coordinate relabel. Separately run the exact3D noncommuting-jet fixture as a representation acceptance test. Passing the latter must not be reported as physical stabilization.

Quality rubric: source binding4/5, mechanisms4/4, discriminating tests5/5, independent-check readiness3/3, scope discipline3/3 =19/20. Subjective confidence in the exact frame algebra98%; no probability is assigned to physical stabilization performance.
