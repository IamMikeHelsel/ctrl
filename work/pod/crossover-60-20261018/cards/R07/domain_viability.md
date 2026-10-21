# R07 scalar viability and known-mass audit

This supplements the first-order allocation result with a distinct second-order normalized model. The integration/comparison argument below is hand-derived, not a kernel-checked general ODE theorem. Exact rational arithmetic checks are separate from that analytic bridge.

## Unavoidable excursion and sharp scalar condition

For a scalar coordinate z with initial z0, speed w0>0, upper ceiling B and acceleration satisfying z''≥−a, a>0, twice integrating gives

z(t)≥z0+w0*t−a*t²/2.

This holds for a classical twice-differentiable path, or under an appropriately stated absolutely-continuous velocity/integrable-acceleration model. At t*=w0/a it implies

z(t*)≥z0+w0²/(2a).

Therefore any trajectory remaining below B for all future time necessarily has available clearance at least w0²/(2a). This necessity does not assume task preservation or that the actual velocity reaches zero at t*. It follows from the pointwise acceleration lower bound alone.

For the scalar double integrator with the full selectable acceleration interval[-a,a], the condition is also sufficient: choose z''=−a until t*, then0. The speed decreases to0 without changing sign, and the attained maximum is exactly z0+w0²/(2a). If w0≤0, choosing acceleration0 stays below the upper ceiling forever. Hence the sharp scalar half-line viability condition is

z0 + max(w0,0)²/(2a) ≤ B.

This is not by itself a theorem for a bounded joint box, obstacle geometry with additional faces, torque coupling, acceleration slew limits or a fixed terminal deadline. Scalar sufficiency needs its selected acceleration to be realizable by the full plant. For a true coast delayδ≥0 before braking, w0>0, the required clearance increases by w0*δ. If a controller acts during the alleged delay, that coast formula no longer applies; its actual committed action must be included.

## Original declared two-joint plant

M=diag(1,2), q''=M^{-1}τ, |τ1|≤1/10, |τ2|≤1/5; no gravity, velocity forces or disturbance. Let z=q1−q2. Every admissible torque, even one abandoning the task q1+q2=0, satisfies

z''=τ1−τ2/2≥−1/5.

At q=(3/10,−3/10), qdot=(1/5,−1/5), z0=3/5 and w0=2/5. Thus z(2)≥3/5+2/5=1>4/5. The obstacle must fail by or at2s for any admissible input defined through that time. The state is instantaneously inside the obstacle and joint bounds, but outside this viability region. The result is stronger than failure of a task-preserving policy.

At q=(1/5,−1/5) with the same velocity, exact maximal braking τ=(−1/10,1/5) gives q1''=−1/10, q2''=1/10. It preserves the task and stops in2s at q=(2/5,−2/5), exactly on z=4/5. The full trajectory remains in[-1,1]², because q1 increases monotonically from1/5 to2/5 and q2=−q1. A positive coast delayδ produces a peak z=4/5+(2/5)δ and fails. This is a constructive sufficient trajectory at the boundary, not a claim that every feasible policy is safe.

## Independent changed-mass check

`domain_mass_check.py/json` reconstructs all six rational fields of `pm_mass_mismatch.json` without importing producer code. Changed known inertia is M=diag(1,101/50), a1% increase of the second mass only. Keeping τ=(−1/10,1/5) gives task acceleration−1/1010, so after2s of braking task position and speed errors are both−1/505. Holding first acceleration−1/10 while canceling it requires τ2=101/500>1/5, outside the declared bound.

Retune both accelerations to magnitude10/101: τ1=−10/101, τ2=1/5. Both input bounds hold and task acceleration is exactly zero. Starting q1=9/50, qdot1=1/5, coasting1/20s, then braking gives:

- Braking duration101/50=2.02s.
- Total issue-to-stop duration207/100=2.07s, including the coast delay.
- Maximum q1=9/50+(1/5)(1/20)+(1/5)²/[2(10/101)]=49/125=.392.
- q2=−q1 and maximum z=98/125=.784<.8.

The maximum is all-time for this explicit trajectory: speed is nonnegative until the exact stop and then remains zero. The producer field `new_stop_time` denotes braking duration. Its unchanged-torque error at2s uses2s of active braking, while the corrected maximum explicitly includes the separate.05s coast; these timing descriptions must not be collapsed.

With the changed mass, the most negative z acceleration if task preservation is abandoned is−201/1010. Preserving the task enforces equal/opposite joint accelerations and limits the magnitude of z deceleration to20/101. The retuned trajectory uses the latter value. Do not reuse the unrestricted scalar acceleration bound as a tight task-preserving bound without this allocation check.

These conclusions rely on exact known inertia and ideal torque delivery. They supply neither robustness to unknown mass nor physical model validation. The critic's coupled-inertia counterexample remains relevant precisely because a kinematic Jacobian-null command is not a dynamic torque-null command.
