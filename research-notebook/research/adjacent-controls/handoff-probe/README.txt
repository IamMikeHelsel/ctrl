Brake-to-terminal-set candidate: a nonempty region outside the old ellipsoid
17 October 2026. Exact-arithmetic diagnostic; not yet a Lean theorem.

Decision significance
The proposed backup can add a concrete capability to the current artifact.
There is a positive-volume initial box outside its energy<=12 region that
passes an exact rational interval check for safe braking into that region.
This supports investing in the handoff proof. It does not establish novelty,
a deployed safety filter, optimal recovery, or robustness to backup disturbances.

Model and candidate
Normalized dynamics: x'=v, v'=a, a'=r(u-a), with fixed r in[9/10,11/10].
No disturbance during the backup; exact states and command are assumed.
Initial box:
  x in[99/100,101/100], v in[49/100,51/100], a in[-1/100,1/100].
Apply u=-1 continuously until T=5/4. Then switch, without resetting state,
to the existing sampled controller, starting its sampling clock at that time.
The backup hold exceeds the old1/5 limit: its safety is checked separately,
not inferred from the old sampled-controller theorem. That theorem applies
only after the terminal-state condition has been established.

Exact-rational diagnostic outputs
* Every point in the initial box has E>=11749189/500000=23.498378>12.
* For the entire backup interval, x lies in[657/800,5297/3200], contained
  strictly inside[-2,2]. These bounds are conservative.
* Terminal energy is bounded above by an exact rational number less than
  11.235 (stored without rounding in results.json), hence strictly below12.

The interval checker covers every r in the stated interval, not only sampled
rates:80 adjacent rational intervals cover it, with8 initial vertices each.
It uses Fraction arithmetic for all acceptance checks. Degree16 and17 Taylor
polynomials bound exp(-q) from above and below. Float conversion occurs only
for a display field. This is not a validated ODE-solver experiment.

Analytic reasoning still to formalize
1. For each r, the existing held-segment formula with u=-1 solves the actual
   ODE and preserves acceleration in[-1,a0], since a0>=-1.
2. Integrating -1<=a(t)<=.01 gives lower position polynomial
   .99+.49t-t^2/2 and upper1.01+.51t+.01t^2/2. The lower is concave and its
   minimum on[0,5/4] is at an endpoint; the upper is increasing there.
3. Taylor's remainder sign proves the two exponential enclosures. Interval
   arithmetic soundness and exhaustive rate-interval coverage need proof.
4. For fixed r, the terminal state is affine in the initial state. The same
   PSD P as the frozen artifact makes terminal energy convex, so its maximum
   over the initial box is bounded by its values at the8 vertices. Existing
   P_psd can support this; the Python checker assumes this argument.
5. The terminal state has E<=12. A time-shifted application of the existing
   uncertain sampled controller theorem then gives future travel safety.
   State continuity, switching semantics and arbitrary-ODE correspondence
   still need an explicit composition theorem. There is no acceleration reset.

No stop-and-hold shortcut
The terminal state can have nonzero velocity and acceleration. Its full energy
is checked rather than assuming that reaching v=0 is a safe terminal condition.
This differs from the one-sided stopping-distance probe in the neighboring
braking-probe folder. Both travel boundaries are covered in this candidate.

Illustrative physical scale only
With nominal tau0=.1s and command scale U=2m/s^2, this initial box corresponds
to position1.98-2.02cm, velocity.098-.102m/s and acceleration+/- .02m/s^2.
The backup lasts125ms and the travel limit is+/-4cm. The conservative position
bound is approximately1.64-3.31cm. No physical robot parameters were measured.

Next gate
Formalize this exact box-to-terminal result before generalizing the guard.
Then make the certified region selectable by measured state, permit a stated
backup error budget, and compare conservatism against an existing backup method.
The desired publication contribution is a useful complete checked composition,
not the invention of maximum braking or interval arithmetic.

Reproduce: python3 research/adjacent-controls/handoff-probe/check.py
The generated results.json records exact values and the frozen P source hash.
