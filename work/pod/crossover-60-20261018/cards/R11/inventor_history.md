# R11 supplement: an admitted startup history and the revision boundary

AI-assisted exact rational calculation, with hand continuum bounds. This supplements the inventor report; it does not change the source controller, physical model, or PM files. Runtime model identity was not supplied.

The PM ramp's initial samples `(x(0),x(-H),x(-2H))=(ε,ε,ε)`, `ε=1/10000`, `H=1/50`, and retained velocity `v0=-1/1000` are constructively compatible with a C1 reference history. On each of the two preceding intervals use local phase `u∈[0,1]` and

`x=ε+v0 H(2u³−3u²+u)`.

Both endpoint positions are ε and both endpoint velocities are v0. Therefore the two intervals join C1, and the new PM ramp at zero starts with exactly the retained velocity. The polynomial identities

`2u³−3u²+u=u(1−u)(1−2u)`,

`6u²−6u+1=6(u−1/2)²−1/2`

show, for every point of each interval, `|x−ε|≤1/200000`, `|x'|≤1/1000`, and `|x''|≤3/10`. At the interior boundary acceleration jumps from `−3/10` to `3/10`; at zero it changes from `−3/10` to zero. These are allowed by C1 position / Lipschitz velocity, with acceleration bounded almost everywhere. There is no jerk bound. A constant-velocity extension before −2H also joins C1, but is only a local prehistory construction, not an all-past bounded-position claim.

This admits **controller startup at zero with authentic buffered samples**, not a fiction that the same delayed controller generated the whole prehistory. If the unchanged ramp controller had already operated on the preceding interval with all relevant samples equal to ε, its velocity would be constantly v0 and its displacement `Hv0=-1/50000`, contradicting equal endpoint positions. The equal triple cannot be justified that way. If a genuinely controller-generated immediate history is desired instead, run two startup intervals first and take the resulting state `(3/50000,1/12500,1/10000)` as the new origin; its retained velocity remains `-1/1000`. The PM Lyapunov energy decreases during those two steps, so its original energy admission remains valid. This does not remove the need for an explicit earliest startup history.

## A target revision cannot reset the retained rate

The constant-target 3-state recurrence relies on the identity that the retained velocity equals `−K` times the specified old error sample. A new target shifts the errors but cannot retrospectively change the velocity already being executed. Recomputing all old errors using the new goal, then assigning `v_old=-K e_old`, introduces a reference-rate jump. Keeping historical errors under their historical targets instead avoids that particular fiction but requires a revised nonautonomous recurrence and truthful target/version labels.

Exact diagnostic: at the same startup state, shift the target from 0 to `1/10` rad. With `K=10`, raw new desired rate is `999/1000`, whereas actual retained rate is `−1/1000`: assigning the former creates a rate jump of 1 rad/s. A separate velocity state and rate/acceleration limiter can preserve C1 reference motion: clip the endpoint to `1/100` and ramp from `−1/1000` over H. This gives acceleration `11/20≤1` and displacement `9/100000`. The entire ramp respects the speed bound because velocity is affine between admissible endpoints.

This is a **declared new reference governor**, not a consequence of the old matrix certificate. Its invariant is reference rate and acceleration admissibility; it does not preserve immediate arrival at the revised target, does not imply a jerk bound, and does not prove physical tracking. The unchanged gap is `999/10000` rad, so speed `≤1/100` alone requires at least `999/100=9.99` seconds to reach the target. A shorter deadline cannot be silently met by relabeling the limited reference as the requested target. The acceleration constraint can only increase this necessary time.

## Evidence and next test

`inventor_history.py` passes exact Fraction assertions for endpoints, matching velocities, incompatible prior-controller displacement, two-step recurrence, and limiter arithmetic, plus 101 rational probes. The continuum inequalities above are hand-derived; the probes are not their proof. No physical experiment or Lean trajectory theorem is claimed.

Recommended next discriminating test: augment the delayed reference state with the actual retained velocity and explicit target versions; prove a switched/forced energy inequality for a declared target-jump budget, then connect it to the inner tracking tube. Negative controls must reject resetting rate, rewriting stored positions to match a new target, and claiming the old constant-target matrix proof after clipping.

Quality grade: 19/20 for this scoped startup/continuity diagnostic. Subjective confidence: 98% in the algebra and scope; no confidence percentage is assigned to untested robot behavior.

A minimal algebraic state bridge makes the retained-rate issue explicit. Set `Z_n=(x_n,x_{n−1},v_n)` with **actual** ramp-start velocity, and let the endpoint command be `v_{n+1}=−K x_{n−1}+d_n`. Exact integration gives

`Z_{n+1}=B Z_n+b d_n`,

`B=[[1,−HK/2,H/2],[1,0,0],[0,−K,0]]`, `b=(H/2,0,1)`.

For the original zero-target constant law, `T=diag(1,1,−K)` maps the PM state to this state, and `B=T A T⁻¹`. Thus its nominal certificate transfers by `Q=T⁻ᵀ P T⁻¹`. A revised target or limiter can be recorded as the explicit forcing `d_n=v_{n+1}+Kx_{n−1}`. The energy difference becomes

`E_{n+1}−E_n=−‖T⁻¹Z_n‖²+2d_n bᵀQBZ_n+d_n² bᵀQb`.

This identity identifies the additional proof obligation; it does not bound `d_n` or establish robust stability. In particular, the target term and limiter discrepancy cannot be omitted. Observation timestamps still determine which target/position was available when the endpoint command was formed.
