# R07 cross-discipline inventor

Minimal intervention should preserve the authoritative task set while intervening whenever the joint state threatens an obstacle, actuator limit or future feasibility. An instantaneous Jacobian nullspace is not sufficient. The strongest new diagnostic here is that a task-tangent velocity on a curved task surface requires a normal acceleration; “irrelevant” motion still consumes actuator capacity.

Model identity: inherited root model, exact identifier unavailable. AI-generated research. This is an explicit two-coordinate toy extension, not a theorem about the earlier scalar plant or a physical redundant arm.

## Provenance and primary reading

Read the frozen R07 card, `intent-contract-07/analyst/motor-control-addendum.md` and `report.md`. The source explicitly says its scalar model has no joint-space redundancy and does not establish a full-arm extension. The stable task/authoritative intent distinction is preserved: an arbitrary preferred joint posture is not silently made an additional task.

Read the opening discussion and model statements of [Todorov and Jordan's primary paper](https://people.eecs.berkeley.edu/~jordan/papers/coordination.pdf). Its stochastic optimal-feedback account motivates permitting task-irrelevant variability. It does not certify our obstacle geometry or actuators, and the paper itself distinguishes computational-level theory from neural implementation. No biological mechanism, diagnosis, energy savings or novelty claim is inferred here.

## Three materially distinct transfers

1. **Quotient goals and exact fibers.** The task is an equivalence class `f(q)=g`, rather than a preferred joint representative. For `f(q)=q1²+q2²`, the level1 fiber is a circle. A rational Cayley parameterization preserves the exact finite task, while one Euler step in a Jacobian null direction generally does not. Preserve the task value and its declared tolerance; do not confuse an uncertainty set of possible goals with permission to choose any goal. Falsifiers: at q=(1,0), tangent step(0,.1) changes f from1 to1.01. At the singular origin, J=0 admits every linearized direction, but `f⁻¹(0)={(0,0)}`; the finite task permits no nonzero motion. Regularity assumptions behind a smooth nullspace/fiber interpretation are essential.

2. **Unexpected transfer from constrained mechanics and actuator allocation.** For exact ideal dynamics `qdot=v`, `vdot=a` and constant squared-radius task, differentiating gives `q·v=0` and `q·a=−||v||²`. The latter is the normal acceleration required by curvature. Preserve the actual second-order plant and total available acceleration/torque when mapping this to control allocation; joint acceleration is not generally physical motor torque. Falsifier: at q=(1,0),v=(0,1), forcing acceleration into kerJ gives q·a=0 and therefore f''=2, violating the task. More sharply, at q=(.01,0),v=(0,.2), preservation requires a1=−4, impossible under ||a||≤1. At speed.1 the required normal acceleration is−1 and consumes the entire acceleration budget. These are declared task-level-family diagnostics, not a retuning of the fixed level1 positive path.

3. **Topology and whole-path acceptance.** Safety constraints carve the task fiber into permitted routes or disconnected components. Preserving the task and checking endpoints does not certify the interior. A path certificate should bind the whole parameter interval and its timing. Falsifier: the right semicircle below has safe endpoints but crosses the forbidden region q1>.8; the left semicircle connects the same endpoints safely. Under the different declared obstacle |q2|≤.6, the safe level1 fiber splits into left/right components: any continuous path from(1,0) to(−1,0) must cross q1=0, where f=1 forces |q2|=1, violating the obstacle. If only f=1 is authoritative, staying in the current safe component is a valid minimal-intervention choice; moving to the other preferred posture is neither required nor feasible under that contract.

## Exact finite-motion experiment

For t∈[−1,1], write

`C(t)=((1−t²)/(1+t²), 2t/(1+t²))`.

The task identity `||C(t)||²=1` is rational and exact. Both C and `(-C1,C2)` connect(0,−1) to(0,1). The right branch reaches(1,0), violating q1≤4/5; the left branch has q1≤0 throughout and respects joint bounds[-1,1]. This is an exact whole-parameter argument, not an inference from the sampled nodes.

With affine timing t=2s/T−1, the joint-speed norm is `4/[T(1+t²)]`. T=4 satisfies ||qdot||≤1; T=3 fails at the midpoint. This only rejects that timing law, not every possible timing law. The affine version has nonzero endpoint velocities and is explicitly not rest-to-rest. `inventor_geometry.py/json` records exact rational nodes, endpoints, singular/Euler negatives, the curvature identity and actuator-budget failure.

## Positive rest-to-rest contract, explicitly an ideal model

A separate declared test uses the left branch and

`t(s)=2(10z³−15z⁴+6z⁵)−1`, `z=s/T`, `0≤s≤T`, T=12.

Its complete toy contract is `qdot=v`, `vdot=u`, no disturbances, q_i∈[-1,1], q1≤4/5, ||v||≤1, ||u||≤1, task f=1, initial q=(0,−1), final q=(0,1), and zero endpoint velocity and acceleration. There is no lag, inertia coupling, torque conversion, friction or sensing uncertainty in this test.

Since the phase derivative is nonnegative, t stays in[-1,1]. The polynomial endpoint derivatives vanish. Elementary bounds give

`|t'|≤15/(4T)`, `|t''|≤30/T²`, `||C_t||≤2`, `||C_tt||≤4`.

By the chain rule, `||qdot||≤15/(2T)=5/8` and `||qddot||≤465/(4T²)=155/192<1`. Exact task and obstacle invariance therefore hold throughout this declared motion with the stated actuator bounds. These all-time bounds are an analytic derivation; `inventor_smooth.py/json` additionally checks21 rational nodes and both endpoint states. The nodes are not the proof of the all-time claim. The path is feasible, not asserted effort-optimal, deadline-optimal or the unique minimal-intervention policy.

The finite clock is part of the contract. If the quintic is continued past T, then at s=2T its phase equals63 and the left-Cayley q1 becomes1984/1985, violating the obstacle. Task equality alone still holds. A post-deadline hold therefore needs an explicit constant tail after T; the zero endpoint velocity and acceleration allow that join. This changed-clock negative is recorded separately and does not invalidate the finite T12 claim.

**Physical-tracking negative:** at the left midpoint q=(-1,0), an outward position error ε=.001 violates the joint lower bound−1. An arbitrary norm-bounded tracking tube therefore cannot turn this zero-margin reference into a robust physical joint-limit certificate. Its task error is `2ε+ε²`. A valid physical adapter must preserve the same constraints while supplying sufficient margin or a suitably correlated invariant error set; it cannot silently expand joint limits or change the task radius.

## Explicitly changed task-level diagnostic

At the PM's request, `inventor_scaled.py/json` separately scales the radius toρ=4/5. This **changes the authoritative task level from1 to16/25**; it is not a repair of the original exact-equality contract. The joint box remains[-1,1] and the obstacle remains q1≤4/5. With a declared isotropic position error bound ε=.1, every joint magnitude is at most.9 and the left-branch physical q1 is at most.1. The actual squared-radius task lies in[.49,.81], so a symmetric task tolerance.17 about.64 suffices. Exact equality still fails: reference(-.8,0) and physical(-.9,0) realize task error.17 with position error.1.

The unchanged T12 timing now has nominal speed bound1/2 and acceleration bound31/48. Separate physical velocity-error≤1/2 and acceleration-error≤17/48 would suffice for the unit bounds, but no such physical tracking theorem has been supplied. Position error alone cannot supply those derivative bounds. This is a conditional geometric margin calculation, not a robust robot acceptance.

## Formal evidence and limitations

`inventor_geometry.lean` separately formalizes the rational Cayley task identity, left-branch obstacle implication, endpoint/midpoint counterexample, singular fiber, linearized/finite and Euler negatives, a conditional curvature actuator contradiction, and the forbidden separating-axis point. Its final compilation passes with ten printed lemmas using only propext/Classical.choice/Quot.sound; a positivity helper is also compiled. The first two failed compilations concerned `noncomputable` definitions and closing the unnamed section; both logs are preserved. Frozen SHA256:636494b205f5f1276cf4b5e3f8d907c44a022efcd0aff214f6e58db18e03a760.

A separate `inventor_timing.lean` now compiles successfully with seven printed lemmas using only propext/Classical.choice/Quot.sound. It proves actual quintic first and second derivatives, phase range, polynomial derivative bounds, endpoints and conditional T12 norm arithmetic. Four failed attempts are retained, including their automatically generated error-state `sorryAx` output; those attempts are not accepted evidence. The successful final log has no such axiom. It does not formalize the entire geometric chain rule and physical plant composition.

The curvature lemma assumes the second-derivative preservation equation; it does not derive it from arbitrary arm dynamics. The forbidden-axis lemma does not formalize the continuous-path intermediate-value bridge. The smooth timing chain-rule and all-time actuator bounds are not Lean theorems in this file. Python exact arithmetic is independent evidence, not a kernel proof. No existing source proof, controller, clock, reference history, hardware or public CLI was changed.

## PM recommendation

GO for a30-minute small acceptance adapter combining the domain researcher's linear allocation theorem with an explicit task/constraint manifest and the nonlinear failure controls above. Require a declared plant order, same initial state, whole-horizon obstacle/joint bounds, actuator limits, uncertainty margins and deadline; returning a hold or rejecting a requested auxiliary move must be reported as such. An authoritative task should specify when joint posture itself matters.

HOLD physical-arm extension until kinematics, dynamics, total actuator constraints, collision geometry and tracking uncertainty are supplied. NO-GO for “all Jacobian-null motions are harmless,” “nullspace acceleration preserves a curved task,” or “safe endpoints certify a safe path.”

Rubric: provenance4/4, distinct transfers4/4, falsifiability4/4, exact testing3/4, scope discipline4/4=19/20. Subjective confidence95% in the stated ideal-model geometric implications; no confidence percentage assigned to an unspecified real arm. Novelty unassessed.
