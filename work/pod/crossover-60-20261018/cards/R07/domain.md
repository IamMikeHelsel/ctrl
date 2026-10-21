# R07 domain: constrained freedom in a task-equivalent set

AI-generated domain research; inherited root model, exact runtime identifier unavailable. Original files unchanged. The old source explicitly has no joint-space redundancy, so no arm guarantee follows from its scalar tracking theorem.

The source asks whether an authoritative task can remain stable while task-irrelevant variation is tolerated. It requires meaningful constraints and preserving executed state/history, and distinguishes advisory estimates from goal revisions. This review preserves that interpretation, but uses a separately declared two-joint kinematic model. Its velocities are not torques, and its exact state is not an unqualified sensor estimate.

The [primary Todorov–Jordan2002 paper](https://people.eecs.berkeley.edu/~jordan/papers/coordination.pdf), pp1226–1228, already describes minimal intervention and even uses X1+X2−X* versus X1−X2 in Figure1. Neither the principle nor our scalar sum-task example is new. That paper motivates selective correction; it does not supply this fixture's explicit obstacle, input and finite-horizon proof.

## Exact positive contract

Assume qdot=u, an exactly retained initial q, constant command u for a declared horizon T>0, task x=q1+q2, desired task velocity v, and symmetric velocity bounds |ui|≤U. A task hold uses v=0. Every command with the desired task rate has the unique representation

u1=v/2+n, u2=v/2−n.

Joint velocity bounds l1≤u1≤h1 and l2≤u2≤h2 are equivalent to

max(l1−v/2,v/2−h2) ≤ n ≤ min(h1−v/2,v/2−l2).

Each geometric halfspace a1*q1+a2*q2≤b must hold initially and at the endpoint. Its endpoint inequality is

T(a1−a2)n ≤ b−a1*q1−a2*q2−T(a1+a2)v/2.

A zero coefficient requires a nonnegative right side; it must not be divided away. Intersecting these scalar inequalities with actuator limits gives [lo,hi]. An empty interval is infeasibility, not a successful hold. For linear halfspaces and this constant-velocity path, initial and endpoint safety are sufficient for every time in[0,T], by convexity. This equivalence does not apply to nonlinear obstacles or accelerated paths.

Project a nominal task-compatible null coordinate n0 to n*=clip(lo,hi,n0). It changes nothing iff n0 already lies in the feasible interval. It minimizes the actual squared joint-velocity intervention because ||u(n)−u(n0)||²=2(n−n0)². This is conditional freedom: task-irrelevant motion is left alone exactly while it meets all declared constraints. Nominal velocity already has the requested task rate; projection onto this scalar interval does not establish optimality relative to an arbitrary nominal velocity without also accounting for the task-normal component.

## Exact discriminating tests

Use q=(2/5,3/5), task hold x=1, horizon1, U=1/4, joint box[0,1]², obstacle q1≤q2. Exact interval: n∈[-1/4,1/10].

- Nominal zero velocity is retained: a deviation from a particular joint posture need not be corrected when the task remains satisfied.
- Nominal(1/10,−1/10) is retained and reaches(1/2,1/2). All constraints hold throughout the full second.
- Nominal(1/5,−1/5) leaves the task exactly unchanged but violates the obstacle at its endpoint. Projection chooses(1/10,−1/10), with squared intervention1/50.
- Task speed3/10 with U=1/10 is infeasible, since the two velocities can sum to at most1/5.
- An initially obstacle-violating state cannot be called safe merely because its endpoint returns to the set.

`domain_allocation.py/json` gives exact Fraction certificates for these five cases and2,835 predeclared-grid equivalences between direct inequalities and interval membership. The grid is a finite checker exercise, not a general theorem. Lean separately proves the general algebraic interval equivalence, projection feasibility/no-intervention/minimum cost, and all-time linear-halfspace implication, with a direct continuous-time numeric fixture theorem. No solver result is trusted.

## Limits and next action

This single hold interval has no retained acceleration or actuator lag. In a torque-controlled arm, the task acceleration depends on M(q)^{-1}τ, velocity-dependent terms and the Jacobian derivative; a vector in ker J need not be a harmless torque. A nonlinear task's instantaneous Jacobian kernel need not preserve the task under a finite Euler step; near a singularity a desired task rate may be unreachable. Other roles test those boundaries separately. None is repaired by relabeling the kinematic command as torque or resetting initial velocity.

A sequence of intervals needs matched endpoints, updated geometry/uncertainty, causal computation and delivery, and an explicit task deadline or progress requirement. Holding an already satisfied task indefinitely is not evidence that a requested move succeeds. Source sensor bounds, fixed0.2mm tube and original scalar controller were not transferred to this new fixture.

Suggested decision: GO for a checked linear kinematic admission layer; HOLD transfer to a dynamic arm until a state/history-preserving viability and actuation contract is supplied. Precise next test: consume the full retained state (q,qdot), enforce braking-distance reserve under coupled actuation, and compare the nominal command against the joint feasible set before any sequential clipping. Quality grade4/5 for this bounded contract. Subjective confidence high in exact algebra, lower in any unproved physical transfer. No novelty claim.

## Upstream nominal policy and fiber test

The nominal law is part of the contract. For the task-only policy take v=k(g−(q1+q2)), with authoritative g, and n0=0. For a satisfied hold, this commands zero regardless of q1−q2. An explicitly authorized secondary motion may instead supply n0, but then the promise is to preserve that motion whenever admissible. A nominal law n0=−k(q1−q2) already recenters posture; feasibility projection may retain it and cannot be advertised as avoiding task-irrelevant correction. Projection solves constraint admission, not task semantics.

Eight exact fiber tests use q1 in{1/10,1/5,2/5,1/2}, q2=1−q1, task rates0 and1/10, T=1, U=1/4 and the same box/obstacle. With task-only n0=0 the selected velocity is always(v/2,v/2); all different q1−q2 values persist. A necessary exception is q=(0,1), v=1/10: the joint2 boundary forces u=(1/10,0), so constraints legitimately break this symmetry. These are in the JSON separately from the five original cases.

`domain_cost.lean` adds the exact decomposition for an arbitrary nominal(u01,u02): squared intervention equals (v−u01−u02)²/2+2[n−(u01−u02)/2]². The first term is constant over admissible n, so the same scalar projection minimizes intervention even when the requested task rate differs from the nominal rate. This algebra does not remove the upstream nominal-policy assumption.

## Acceptance checkpoint

Final frozen `domain_allocation.lean`11 and `domain_cost.lean`3 declarations compile exit0 with only propext, Classical.choice and Quot.sound. The allocation file's earlier namespace/conjunction-tactic failures are preserved in attempt logs and excluded from acceptance. `domain_lean_acceptance.json` records source hashes and declaration counts. The independent critic is replaying these14 at this checkpoint.

I also independently compiled the critic's five `critic_dynamics.lean` statements and checked their binding. They establish explicit algebraic torque/null-space, nonlinear finite-step, singular-fiber and braking witnesses; they do not claim a generic ODE comparison theorem. This replay is `domain_critic_replay.log`, with exact source hash in the acceptance JSON.

Reproduction from `lean/`: `lake env lean ../work/pod/crossover-60-20261018/cards/R07/domain_allocation.lean` and the analogous command for `domain_cost.lean`. From repository root: `uv run --no-project --python /usr/local/bin/python3 python work/pod/crossover-60-20261018/cards/R07/domain_allocation.py`. Scoped Ruff check and format check pass. Root owns integrated campaign checks; none is inferred from these isolated checks.

The additional parent-requested quantifier audit is in `domain_viability.md`: the initial q=(.3,−.3), qdot=(.2,−.2) violates the obstacle by2s under every bounded torque, even if task preservation is abandoned. The sharp scalar stopping-clearance criterion and its constructive sufficiency assumptions are separated explicitly. `domain_mass_check.py/json` independently reproduces the known1% changed-mass retuning, with maximum q1=.392, braking duration2.02s and total duration2.07s including the.05s coast. The general ODE comparison remains hand-derived; exact arithmetic does not replace that bridge.
