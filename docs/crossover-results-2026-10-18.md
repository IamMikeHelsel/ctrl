# Geometric control crossovers for ctrl

The useful common object is a reduced search problem **with a checked route back to the original
constraints**. This session produced a four-case structural reproof of the existing Erdős 834
witness and a continuous-time robust braking certificate for a scalar control template. Neither
establishes a new open-problem solution or a universal controller. Both make the next search more
precise and easier to audit.

AI disclosure: OpenAI Codex developed the experiments, Lean proofs, and this exposition on
2026-10-18. The separate program-manager subagent wrote the
[program report](crossover-program-report-2026-10-18.md). The hypergraph is Li's existing construction;
the control results formalize standard comparison and stopping-distance reasoning. Scientific
novelty has not been established.

## Eight crossovers and what they delivered

| Crossover | Concrete result | Evidence and limit |
|---|---|---|
| Hypergraph coloring → quadratic energy | A 3-edge monochromatic indicator is quadratic on binary variables; Li's instance has minimum energy 1, weighted maximum cut 42, minimum Ising pair sum −18. | General local identities checked in Lean; exact instance spectrum replayed in Python. No continuous-relaxation optimum is substituted for the discrete problem. |
| Energy search → structural contradiction | Normalize one color, then three binary branch nodes give four contradiction leaves. | Integrated into the exact existing 834 solution; an independent Python checker replays every force and branch. Fewer case leaves, not a claim of shorter source or faster compilation. |
| Criticality → private violation certificates | Each deleted-edge coloring violates exactly its removed edge; positive vertex degree makes the vertex-deletion table redundant. | Generic Lean lemmas; removed the nine-row vertex witness table. Also applies to minimally infeasible families of control constraints. |
| Template abstraction → simulation contract | A template invariant transfers along an anchor trace when every realized anchor transition has a related template successor and related safe states imply actual safety. | General Lean theorem. It exposes, rather than solves, morphology-specific realization obligations. |
| Barrier search → exact braking boundary | The scalar stopping-distance set has matching safety and impossibility certificates under a bounded input and adversarial acceleration disturbance. | Continuous-time derivative comparison and algebraic boundary checked in Lean. Classical trajectories only; no robot, delay, or impact model is supplied. |
| Null-space motion → actuator headroom | At fixed command `u₁+u₂=1` with each actuator in `[0,1]`, centered allocation maximizes symmetric per-actuator box radius at `1/2`. | Lean upper bound and attainment certificate. Independent perturbations need not preserve the commanded sum. This is actuator headroom, not extra net wrench authority. |
| Port interconnection → residual and reset budgets | Summed energy inequalities retain a port mismatch term; discrete events preserve a budget only if each event meets its bound. | Lean algebra and induction. Physical energy balance and reset inequalities still need derivation for the chosen system. |
| Anchor allocation → convex feasibility certificates | Affine inequality certificates interpolate between feasible allocations in a fixed mode; endpoint safety has an exact bounded-input criterion but can miss intersample collision. | Lean interpolation, robust endpoint iff, and explicit counterexample. A polytope atlas/controller implementation remains future work. |

## The strongest mathematical result from this session

For a binary coloring `x`, define `E(x)` as the number of monochromatic hyperedges. For a triple,

\[
x_i x_j x_k+(1-x_i)(1-x_j)(1-x_k)
=1-x_i-x_j-x_k+x_ix_j+x_ix_k+x_jx_k.
\]

With signs `sᵢ=1−2xᵢ` and pair multiplicities `wᵢⱼ` counting hyperedges containing the pair,

\[
4E(x)=m+\sum_{i<j}w_{ij}s_i s_j,
\qquad C(x)=2(m-E(x)).
\]

Here `C` is the weighted cut value and `m` is the number of hyperedges. Every mixed triangle
contributes two cut pairs; every monochromatic triangle contributes zero. The reduction is exact
for 3-uniform weak coloring. It does not automatically extend to higher uniformity, and pair
multiplicities alone do not identify which hyperedges are deletion-critical.

For the actual 9-vertex, 22-edge witness read from the existing solution:

- Total pair weight is 66; degrees are `10,7,7,7,7,7,7,7,7`.
- Minimum monochromatic-edge count is 1; there are 26 minimizers with vertex 0 fixed to color 0.
- Maximum weighted cut is 42. A proper two-coloring would require 44.
- Every one of the 22 edges has a coloring whose only monochromatic edge is that edge.

The quadratic representation suggested optimization bounds, but the effective certificate came
from interpreting zero energy as not-all-equal constraints and propagating them. Write `i=b` for
vertex `i` having color `b`. After normalizing `0=0`, the complete contradiction tree is:

| Decisions | Forced assignments in order | Monochromatic edge |
|---|---|---|
| `1=0`, `3=0` | `2=1, 8=1, 5=1, 7=1, 4=0, 6=0` | `{0,4,6}` |
| `1=0`, `3=1` | `2=1, 8=1, 7=0, 5=0, 4=1, 6=1` | `{4,6,8}` |
| `1=1`, `5=0` | `3=1, 6=1, 2=0, 8=0, 7=1, 4=1` | `{4,6,7}` |
| `1=1`, `5=1` | `2=0, 6=0, 7=1, 4=1, 8=0, 3=0` | `{0,3,8}` |

Every force uses two equal-colored vertices of an existing edge. The third must have the other
color. Complementation covers color `1` at vertex 0 without additional cases.

This replaces the original 512-coloring enumeration inside the non-two-colorability proof.
Finite kernel checks still establish edge membership, uniformity, degree, three-colorability,
and the edge-deletion witness table. The solution still proves exactly
`Challenge.Erdos834.statement`; the challenge and its approval marker are unchanged.

### Why the vertex table was unnecessary

For each vertex `v`, choose an incident edge `e`, possible because its degree is positive. A coloring
of `H.erase e` also colors the smaller family of edges avoiding `v`. This implication does not use
3-uniformity, the number of vertices, or a special property of Li's construction.

The stronger abstract observation is that minimal infeasibility gives a private violation witness
for every constraint. An infeasible family cannot have zero violations, while deleting constraint
`i` supplies an assignment with exactly one violation, at `i`. The helper file formalizes both this
statement and its finite-set certificate. In control optimization, the analogous output is an
irreducible conflicting constraint family together with witnesses showing why each member matters.

## A control certificate with matching limits

Use distance `q` from a one-dimensional forbidden half-space and velocity `v`, with

\[
\dot q=v,\quad \dot v=u+d(t),\quad u\le U,\quad d(t)\ge-\delta,\quad a=U-\delta>0.
\]

For the usual symmetric disturbance interpretation, also choose `δ≥0` and `|d(t)|≤δ`.
The sufficiency proof needs only the lower bound. Assume maximum braking `u=U` is admissible,
the measured state is exact, and classical differentiable trajectories exist for all times
being considered. Then the exact robust viability boundary for this scalar setting is

\[
\mathcal K=\{(q,v):q\ge0\ \land\ (v\ge0\ \lor\ v^2\le2aq)\}.
\]

The formal statements require `HasDerivAt` at every nonnegative time. They do not cover arbitrary
measurable disturbances or ordinary piecewise-constant acceleration jumps at their switching
instants. An extension to absolutely continuous trajectories with almost-everywhere dynamics, or
an explicit piecewise gluing theorem, remains to be proved. Trajectory existence is assumed.

The proof has three parts:

1. **Algebraic boundary.** The polynomial `q₀+t v₀+(a/2)t²` is nonnegative for all `t≥0` iff
   `(q₀,v₀)∈K`. Completing the square handles inward velocity; evaluating at `t=−v₀/a` proves
   necessity. Its exact constant-braking step preserves membership in `K`.
2. **Actual trajectory comparison.** If `q'=v` and `v'≥a`, derivative monotonicity twice gives
   `q(t)≥q(0)+t v(0)+(a/2)t²`. Thus maximum braking is safe for every admissible time-varying
   disturbance realization satisfying the displayed regularity.
3. **Impossibility outside.** Under the admissible constant disturbance `d=−δ`, any input
   satisfying `u(t)≤U` gives the reverse comparison. Outside `K`, some nonnegative time has
   `q(t)<0`. No such controller can promise robust safety from that state.

This is a useful template contract: a robot-specific allocator must establish a conservative
achievable acceleration bound, disturbance bound, and the distance/velocity dynamics. A distance
to a curved obstacle generally introduces additional derivative terms; inserting an arbitrary
task-space coordinate into this theorem is not justified. Underactuation, contact switching,
sensor error, latency, and actuator slew limits also require new modeling and transfer proofs.

### Why endpoint checking was rejected

The exact held-input endpoint condition is
`q + Δt v + (Δt²/2)(U−δ) ≥ 0`. It is necessary and sufficient for the existence of an input in
`[lo,U]` that protects that endpoint against a constant disturbance in `[-δ,δ]`, assuming
`lo≤U` and `δ≥0`.

But `q(t)=1−6t+6t²` has `q(0)=q(1)=1` and `q(1/2)=−1/2`. Both endpoints pass while the trajectory
crosses the forbidden boundary. The stopping-distance result addresses continuous time instead.
Neither a finite sample grid nor a QP returning a feasible endpoint substitutes for that argument.

## Approaches that failed and what the failures mean

**Clique-cover relaxation.** Cover the weighted graph with nonnegative weighted cliques and use
`maxcut(Kₖ)≤floor(k²/4)` on each. A numerical LP returned 44. An exact rational dual certificate
was then checked against all 118 supported cliques; its objective is also 44. The original 22
triangles provide a matching primal cover. Thus this relaxation cannot certify a bound below 44
for this instance. The replay uses Python `Fraction`; a Lean LP-duality proof was not added.

**Basic semidefinite relaxation.** A numerical diagonal-majorant SDP returned an upper bound of
approximately 44.51890455. This does not rule out 44 and does not explain the discrete optimum 42.
No rational PSD certificate was produced, so this is only a diagnostic search outcome.

**Universal hardware erasure.** A shared balance law does not establish a shared feasible control
set. The reduced-order CBF tutorial explicitly discusses additional underactuation assumptions;
the relevant transfer obligation remains robot-specific.
([Cohen, Molnar, Ames](https://arxiv.org/html/2403.09865v1), sections 5.3 and 8.)

The next search should therefore try certificate-producing discrete branching or a strictly
stronger relaxation, rather than spend more compute rerunning either unsuccessful bound.

## Corrections to the supplied synthesis

- The cited 2019 template/anchor paper develops approximate simulation and a constrained balancer
  example. It should not be cited as a Riemannian-submersion formalization.
  [Kurtz et al.](https://arxiv.org/abs/1909.09693)
- PHRetune derives controller gain adjustments from learned port-Hamiltonian models and
  demonstration budgets. That does not establish a universally verified port controller.
  [Yang et al.](https://arxiv.org/abs/2610.05755)
- OSCBF provides a task-consistent safety-filter framework; using it still requires the relevant
  dynamics, constraints, and feasible actuation.
  [Morton and Pavone](https://arxiv.org/abs/2503.06736)
- The bounded-input backup-CBF paper is an appropriate reference for enforcing feasible control
  while interpolating a nominal and backup controller. The elementary affine interpolation lemma
  here does not formalize that paper's complete method.
  [van Wijk et al.](https://arxiv.org/html/2510.05436v1)

## Reproduce and inspect

```sh
uv run python -m experiments.crossover
uv run ruff check .
uv run ruff format --check .
uv run pytest -q
cd lean
lake env lean Research/ControlCertificates.lean
lake build
cd ..
uv run ctrl check --all
```

- [834 solution](../lean/ErdosLab/Erdos834.lean): the four-case proof and unchanged statement binding.
- [Reusable math lemmas](../lean/ErdosLab/Erdos834/Coloring.lean): recoloring, criticality, and energy identities.
- [Control lemmas](../lean/Research/ControlCertificates.lean): exact assumptions and axiom output.
- [Exact experiment](../experiments/crossover.py) and [saved evidence](../work/834/certs/crossover.json).
- [Certificate mutation tests](../tests/test_crossover.py): false force, missing branch, false conflict,
  and unexpected source-expression rejection.

`ctrl check --all` intentionally still requires human approval of the existing 834 challenge.
Research is a checkpoint build target, not an approved physical-plant challenge. This session did
not deploy a controller, submit a mathematical result, or run hardware acceptance tests.

Observed final checks: `lake build` succeeded; all 16 control and seven mathematical helper lemmas
printed only allowed axioms or none; the 834 statement binding and axiom/token audits passed.
`ctrl check --all` exited 3 solely for `NOT_APPROVED`. Ruff and format checks passed; pytest reported
49 passed and one integration test deselected in 0.49 seconds. No current-revision Spark check
was performed. The full build retains an existing missing-module-docstring warning in `ErdosLab.lean`.
