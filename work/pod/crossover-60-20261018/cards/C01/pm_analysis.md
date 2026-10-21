# PM synthesis and acceptance boundary

AI-written; inherited root model, exact runtime identifier unavailable. C01 initial review.

The frozen question concerns a slow full-command filter meeting the unchanged 0.2 mm
tracking task while improving actual jerk or command variation. Improvements in reference
jerk, compensated error, or filter input do not answer this question. A change to feedforward
placement is a separately identified alternative, not a demonstrated solution for that class.

The three substantive transfer directions are moment matching with causal polynomial jets,
pole reassignment with filter memory included in the plant, and the unexpected interpretation
of a positive smoothing kernel as a distribution of delays. Convex sampled-family minimization
and viability/error-budget reasoning provide additional discriminating tests. This is an
application and comparison exercise; novelty is not established.

## Mechanism and scope

At r=80, lambda=20, the old compensated controller matches the direct controller's DC
jerk-to-error gain exactly. Its denominator is nevertheless close to the Hurwitz boundary:
lambda must exceed (-25+5 sqrt(153))/2, approximately18.423. Changing jerk feedforward cannot
move these poles. Snap feedforward removes the remaining numerator's derivative term and
matches the first three low-frequency series coefficients, but neither that nor pole retuning
addresses the full startup transient. The initial filtered command is zero; the direct command
starts algebraically at5/48. No fictitious prehistory or initial impulse is admissible.

Root independently constructed a derivative blend in physical coordinates, with unknown
disturbance excluded from the controller's nominal derivative calculation. The six-law screen
reproduces the direct and compensated baselines. Alpha>=1/4 meets sampled tracking but all
five filtered variants lose the peak-jerk and variation comparison. Critic independently
reproduced its physical ODEs using DOP853 and rejected state-reset/missing-term controls.

The filter equation alone is not a slew constraint: u'=20(c-u) allows an arbitrary desired
derivative d by setting c=u+d/20. Such cancellation cannot establish a genuine slow-bandwidth
benefit merely from the coefficient20. Actual jerk and actual command variation remain the
acceptance metrics; adding fast derivatives or moving the filter must be disclosed.

## Two analytic bounds

For any physically admissible x with zero initial position, velocity and acceleration and
|x'''|<=J, x(t)<=J t^3/6. Tracking requires x(t)>=q(t)-1/5000. At the exact reference time
51/200 this gives J>=438970/44217, approximately9.927629645. The critic strengthened the
same argument at t=23/80 to60499239/6083500, approximately9.944807923. These are necessary
bounds, not optimal or achievable values. They rule out large peak-jerk savings irrespective
of controller family. The integration argument is ordinary mathematics with rational
arithmetic, not a Lean proof.

For the separately relocated filter z'=20(j-z), z(0)=0, gain1/960, fixed r=80, the actual error
satisfies (D+40)^3 e=-j/6+z/12+80w with e(0)=e'(0)=e''(0)=0. The reference has |j|<=10,
independently checked by rational Bernstein coefficients. Thus |z|<=10. The positive kernel
t^2 exp(-40t)/2 has integral1/64000, so |e|<=(10/6+10/12+4/5)/64000=33/640000 m,
or0.0515625 mm, for any bounded |w|<=.01. This certifies a model-level tracking margin by
hand under these assumptions. It certifies neither jerk/variation improvement, uncertain
actuator rate, sensor noise, saturation, delay, nor a physical robot. Direct's analogous
bound is37/960000 m. No formal kernel acceptance is claimed.

## Source and prior-art checks

The original enclosure builder's 'independent review pending' label is stale; the existing
grader accepted it, and today's critic replayed that separate implementation with mutations.
Original source files remain unchanged.

Primary literature checked during this review:

- [Farrell et al., Command Filtered Backstepping](https://doi.org/10.1109/TAC.2009.2015562):
  explicitly analyzes filtering's effect on tracking and uses compensated error dynamics.
  This is prior art for compensation, not validation of our frozen controller or its task.
- [Xiao and Belta, high-relative-degree barrier functions](https://arxiv.org/abs/1903.04706):
  motivates retaining the derivative chain and checking feasible invariant sets. It does
  not make a position tube invariant merely by clipping jerk.
- [Bemporad, Reference governor for constrained nonlinear systems](https://doi.org/10.1109/9.661611):
  a governor can handle the reference online. Altering this task's frozen reference would
  change the question, so our governor test changes actuation only.

No exhaustive novelty search, physical validation, or general filter impossibility is claimed.
