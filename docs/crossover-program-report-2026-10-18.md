# Crossover research: program manager report

Date: 2026-10-18, America/Los_Angeles. Status: completed research checkpoint; human approval pending.

This report is AI-written by the program manager subagent requested by Mike. It explains the
choice of experiments and the evidence needed to count them as successes. It is not a claim of
scientific novelty or a hand-written mathematical exposition.

## What we are trying to achieve

The supplied note proposes a useful direction: discover mathematics on a small shared model,
then prove that a particular physical system implements that model closely enough. The same
discipline applies to finite mathematics: search in a convenient representation, then check the
result against the original statement. In both cases the bridge is part of the proof.

The request for “a breakthrough or 8” is interpreted as permission to explore several substantive
hypotheses, not a target number of claims. Success requires an explicit statement, reproducible
evidence, and clearly stated limits.

## Why these experiments

| Workstream | Hypothesis | Why spend effort here | What would count |
| --- | --- | --- | --- |
| Hypergraph → MaxCut/Ising | A difficult coloring condition becomes an exact discrete energy bound. | Erdős 834 already supplies a small concrete witness and an existing Lean proof to compare against. | An exact identity plus a certificate for that witness, without changing the challenge. |
| Sampled control template | A low-dimensional bounded-input model can expose safety conditions that survive sampling and bounded disturbance. | It isolates the common physics before robot-specific complexity. | A theorem with explicit input, sample-time, disturbance, and initial-state assumptions. |
| Template → anchor | Transfer is sound when the realized motion satisfies a quantified simulation or error contract. | This is the attachment's most consequential missing step. | A precise implication from anchor assumptions to template guarantees. |
| Passivity and hybrid composition | Energy and reset budgets can make component-level guarantees compose. | Contact and actuation errors otherwise invalidate smooth ideal-model arguments. | Separate inequalities for continuous evolution, interconnection, and reset events. |

The active repository contains a finite-mathematics pilot, not a specified robot plant. A universal
controller for arbitrary robot URDFs is therefore not an available acceptance test tonight.

## Evidence standards

We distinguish four outcomes:

1. **Kernel-checked theorem:** Lean accepts the stated implication under disclosed assumptions.
2. **Exact computation:** exhaustive or rational computation produces reproducible finite evidence;
   it still needs Lean rechecking to satisfy the repository's mathematical proof contract.
3. **Candidate:** a useful derivation, numerical result, or formulation still missing a proof obligation.
4. **Unsupported:** a claim whose assumptions, provenance, or evidence are insufficient.

A theorem about a simplified control model is not evidence of physical robot acceptance. A proof
of an existing example is not a new solution to an open mathematical problem. Passing an axiom
audit does not itself establish that the formal statement matches the user's intended statement.

## Starting state and constraints

The existing Erdős 834 part-ii work checks Li's 9-vertex, 22-edge hypergraph. Its recorded checks
passed build, forbidden-token, axiom, and statement-binding checks, while failing `NOT_APPROVED`.
Human statement approval remains separate from proof construction. Existing CLI/Spark changes
were already present and are preserved.

No challenge statement is to be edited or human approval fabricated. The supplied note's broad
physical equivalence claim needs qualification: common momentum or energy equations do not erase
contact feasibility, actuator limits, singularities, tracking error, or impact resets.

## What the source check changed

The main research direction is supported, but several details in the pasted synthesis need repair:

- The cited 2019 template/anchor paper uses **approximate simulation**, with explicit error bounds
  and contact constraints. It does not present the result as the claimed Riemannian-submersion
  construction. This supports making the transfer error a first-class proof obligation.
  [Kurtz et al., full text](https://arxiv.org/html/1909.09693v1).
- The reduced-order CBF tutorial explicitly develops methods to construct full-system CBFs from
  simpler models. This supports the selected direction, without establishing an unconditional
  transfer to arbitrary robots. [Cohen et al.](https://arxiv.org/abs/2403.09865).
- EmbodiSteer's current abstract reports a **46.1-percentage-point** collision reduction across
  nine simulated robots; **90.0 percentage points** refers to two physical robots in constrained
  scenarios. The pasted note merges these populations and describes a percentage-point result as
  a percentage. Its method is inference-time joint-space guidance for learned policies, which is
  different evidence from a universal CBF theorem.
  [EmbodiSteer v2](https://arxiv.org/abs/2606.12965v2).
- PHRetune is an offline controller-gain selection method using a learned port-Hamiltonian model
  and demonstration-derived budgets. That is motivation for energy budgets, not evidence that
  arbitrary hardware interconnections inherit a universal safety guarantee.
  [PHRetune](https://arxiv.org/abs/2610.05755).
- Franchi's aerial-manipulation review emphasizes coupling among support, locomotion, stabilization,
  and environmental interaction. Its abstract cautions against treating aerial manipulation as
  ordinary manipulation mounted on a flying base. That supports retaining embodiment-specific
  feasibility in the anchor contract. [Franchi](https://arxiv.org/abs/2607.04719).

The remaining arXiv identifiers in the note resolved to relevant paper titles. This was a source
identity and scope check, not a full replication or literature novelty review. The PMC page was
blocked by its browser check, so its contents were not independently verified in this pass.

## Resource decisions

Mike authorized use of available usage and cloud credits on promising paths. That removes an
artificial spending constraint; it does not make expensive search inherently useful. Small exact
examples, counterexamples, and proof obligations are the first filters. Remote search is justified
when a measured bottleneck and an independently checkable certificate format are identified.
This session used local computation and the current assistant/browser tools. It launched no Spark
or additional paid cloud compute. Temporary local numerical packages helped discover candidates;
the saved exact replay does not depend on those optimizers or change the package manifest.

## Results

The control work is in
[`lean/Research/ControlCertificates.lean`](../lean/Research/ControlCertificates.lean): sixteen
compiled lemmas, including continuous-time lower and upper comparison, with printed axiom
dependencies within the default tier; the simulation-transfer lemma uses no axioms. Seven new
generic mathematical helpers also compiled in
[`Coloring.lean`](../lean/ErdosLab/Erdos834/Coloring.lean), for 23 new helper/control lemmas total.
These are the useful control findings:

| Finding | What is checked | Practical meaning and limit |
| --- | --- | --- |
| Template transfer | An invariant transfers when every realized anchor step has a related template successor. | Exposes the universal obligation on disturbances and realized dynamics; it does not prove a robot satisfies it. |
| Error margin | An already-established output error bound is absorbed by sufficient barrier margin. | Tracking accuracy consumes a quantifiable safety margin. Deriving the error bound remains separate. |
| Robust sampled endpoint | An exact scalar feasibility condition under bounded input and constant step disturbance. | Quickly rejects impossible requests, but establishes only endpoint safety. |
| Intersample counterexample | A trajectory is safe at both sample endpoints and unsafe in between. | Endpoint-only tests are insufficient even with exact dynamics. |
| Braking boundary | An exact all-time stopping-distance condition, plus lower and upper comparison arguments for differentiable trajectories. | Maximum braking is safe inside the set; a worst admissible disturbance forces violation outside, under the displayed dynamics and regularity. |
| Actuator headroom | The centered allocation maximizes symmetric box headroom for a two-actuator example. | Quantifies one benefit of redundancy. Independent perturbations do not preserve the task sum unless their sum is zero. |
| Energy and resets | Residual internal power and per-event energy increments compose as explicit budgets. | Ideal power cancellation and harmless impacts may not be silently assumed. |
| Convex interpolation | Feasible endpoint inputs remain feasible under interpolation through a fixed affine inequality. | Useful for a fixed constraint polytope; changing contact modes require new constraints. |

These eight explanations group sixteen formal lemmas. They are **not eight scientific
breakthroughs**. Their value is making hidden assumptions and failure modes inspectable. There are
zero physical-plant validations in this work. The continuous-time extension assumes classical
trajectories and does not prove their existence. Arbitrary measurable disturbances and generic
control jumps need an almost-everywhere or piecewise extension.

The math search produced a structural improvement: after normalizing complementary colors,
NAE propagation reduces the non-colorability explanation to three branch nodes and four
contradiction leaves, compared with the old proof's exhaustion of 512 assignments. The modified
[`Erdős 834 solution`](../lean/ErdosLab/Erdos834.lean) has compiled, and the separate vertex-deletion
witness table has been removed. The full repository build passed; human statement approval is
still required.

The mechanism is easy to inspect: a hyperedge forbids its three vertices from all having the same
color. Once two have the same color, the third is forced. Swapping both color names changes
nothing, so one vertex can be fixed first. Only three further binary branching decisions are then
needed across the entire tree; each of the four resulting paths forces a forbidden monochromatic
edge. This compresses the logical case analysis, even though spelling out the reason takes more
source lines than asking Lean to enumerate every assignment. No checking speedup is claimed
without a controlled measurement.

Vertex deletion also has a reusable explanation. Choose an edge containing the deleted vertex.
Edge criticality supplies a coloring after removing that one edge. Removing every edge through
the vertex leaves fewer constraints, so the same coloring still works. Positive degree guarantees
that the first edge exists. A separate table of nine vertex-deletion colorings is unnecessary.

The exact replay in [`experiments/crossover.py`](../experiments/crossover.py) reads the actual Lean
witness and records its results in [`crossover.json`](../work/834/certs/crossover.json): 256
complement-normalized colorings, a minimum of one monochromatic edge, weighted MaxCut 42, Ising
pair-sum minimum −18, and 26 normalized minimizing colorings. An independent propagation-tree
checker verifies the search result. Five focused tests passed, including rejection of a wrong
forced color, a missing branch, and a false contradiction. The PM independently inspected the
replay and mutation tests; the implementation agent ran them.

The weighted-clique relaxation was a useful failed hypothesis. Its optimum is 44, too weak to
exclude a proper coloring: an exact rational dual is checked against all 118 supported cliques,
and the original 22 triangles supply a matching primal cover. This is exact Python arithmetic and
an ordinary primal/dual argument, **not a Lean-checked theorem about LP duality**. A separate
numerical SDP bound of approximately 44.5189 was also insufficient; it is only numerical evidence.
These outcomes explain the switch to structural branching instead of more effort on the same
relaxations.

## Validation and delivery boundary

The implementation agent reported a clean Ruff lint check and format check, and 49 passing Python
tests in 0.49 seconds, with one integration test deselected. The five new certificate tests are
included in that total. Source-token audit found no forbidden tokens in the three touched proof
files. The challenge file has no diff.

The final `lake build` exited 0. The final `uv run ctrl --json check --all` passed build, token,
axiom, and exact statement-binding checks, and exited 3 solely because the existing challenge still
requires human approval (`NOT_APPROVED`). The solution's axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`; its type remains `Challenge.Erdos834.statement`. The build
reported only an existing missing-module-docstring warning. The PM reviewed source and evidence;
the implementation agent executed these checks.

This is a successful proof-structure improvement and a useful control proof foundation. It is not
an approved mathematical submission, a new open-problem solution, or a controller validated on
hardware. See the [technical results](crossover-results-2026-10-18.md) for the exact equations,
four-leaf contradiction table, and reproduction commands.

## How to ask for the next round

The most useful follow-up prompts are narrow enough to have a decisive acceptance test:

- **For controls:** “Use this plant model and actuator/contact bounds, this sample period and
  latency bound, and this obstacle or joint-limit safe set. Prove a nonempty invariant set and
  quantify the maximum disturbance and tracking error it tolerates. Give a counterexample when
  the assumptions fail.” A URDF alone does not specify disturbance, delay, friction, or the safety
  objective.
- **For math:** “Take this exact approved statement. Use the energy representation to seek a
  smaller structural certificate, have Lean recheck it, and compare certificate size and checking
  cost with the existing proof.” This makes a useful improvement distinguishable from a new
  presentation of the same computation.
- **For larger search:** “Choose one unresolved target with a finite certificate format. Benchmark
  the small case, then scale on Spark through `ctrl spark`. Report the strongest checked result,
  the best unresolved bound, and which experiment would distinguish the next two hypotheses.”

Asking for a breakthrough is enough to authorize exploration. Naming the plant or formal target
and the falsification test is what makes the next round more likely to produce a usable result.
