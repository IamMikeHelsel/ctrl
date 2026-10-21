# S12 — Uncertainty-preserving action under ambiguous attribution

**PM: GO for a checked separation between joint evidence and compact decision certificates.**
Physical/dynamic use remains HOLD. Review quality95/100: faithfulness4, reproducibility4,
discriminatory value4, independent critique4, actionability3 (19/20). Subjective confidence
is high in the stated static results; practical benefit and novelty are unestablished.

AI-written. Root PM plus inventory_math/domain, inventory_vision_robotics/inventor and
inventory_controls_safety/critic. All inherited the root model; exact runtime identifiers
unavailable. No model-family diversity claimed. Real timing is in ../../state.json and
../../activity.jsonl; preparation and inactive gaps are excluded.
Actual S12 substantive elapsed time:619.640815seconds (10minutes20seconds).

## Original question and strongest prior evidence

Can a safety decision remain sound when source attribution stays nonidentifiable and sensor
observations contain duplicated shared information? The source is a static, signed, scalar
synthetic model with known wheel gain1, w,d in[-2,2], q=lambda*d and lambda in[1/5,3/10].
Baseline w+d lies in[9/10,11/10]; separating w+q lies in[3/5,13/20]. A correction c leaves d
and transfers unchanged. Acceptance requires |w+c|<=1/8 and |w+c+rho*d|<=3/4 for every retained
world and every rho in[0,1]. Original actions are-1/2 and-1. Heldout data is not identification.

Original sources under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/`:

- `source-attribution/{challenge.txt,model.json,experiment.py,results.json,check.py,readme.txt}`.
- `adjacency-review/coupled-measurements.txt`.

The investigated source already has56 exact endpoint certificates, one infeasibility
certificate and eight action checks, including nonempty and branch-completeness guards.
Fresh replay passes. The original scalar heldout interval check is sound for its single
surviving convex branch; we found no existing hull bug. Original model SHA256:
9f2ff239496551e75477405e91048a69d91eb3759d949a94501e3ebc13d9b867.

## Creative transfers and discriminating tests

1. **Abstract interpretation and objective-dependent coordinates.** Preserve full joint worlds
   for observations; certify only the supports needed by the decision. For this predicate,
   (w,b=w+d) and four marginal endpoints are lossless, since the mixed response is a convex
   combination of w+c and b+c. A source-coordinate(w,d) box instead falsely rejects-1/2,
   reporting449/560>3/4 where the exact mixed upper bound is3/5.
2. **Idempotent evidence/provenance.** Duplicating a bounded observation100times changes no
   exact feasible world. Pretending four copies halve its deterministic error bound accepts
   a new diagnostic action-23/50; an original retained world then has wheel residual
   51/400>1/8. No claim of a statistical independence model is used.
3. **Unexpected zero-error communication analogy.** Worlds confusable through all available
   readings must share a safe action for an observation-only policy to work. Perfect source
   sensing need not identify enough for the decision; repeated packets cannot separate
   worlds with the same information. Two individually controllable synthetic worlds have
   disjoint safe-action intervals while sharing a perfect separating reading and an allowed
   heldout reading. Their observations differ from the original experiment and are labeled.
4. **Decision-focused experiment design.** At the original readout center5/8, prospective
   separating precision epsilon<=43/1000 permits some common static correction; the original
   action-1/2 needs epsilon<=13/400. These are exact conditional thresholds, not a universal
   promise for every possible readout or proof of physical sensor accuracy.

Each transfer's assumptions, failure modes and artifacts are in inventor.md and pm_analysis.md.

## Results and proof boundaries

- The exact safe correction interval is[-143/280,-37/80]. Lean proves sufficiency under the
  original real-valued common-leakage and measurement constraints, for all rho. Original
  feasible endpoint worlds prove necessity. Thus source attribution can remain ambiguous
  while the static action is certified. The original-1/2 is inside; -1 is outside.
- A decision box must not become the evidence state. Its corner(w,b)=(27/70,9/10) lies within
  both marginal ranges but has no original compatible joint world. Lean proves the
  incompatibility and separately proves losslessness of the box for the frozen action
  predicate, assuming certified containment and endpoint attainability.
- Generic Lean statements enforce truth-preserving updates, duplicate idempotence, nonempty
  acceptance, complete branches and a shared joint witness for heldout compatibility.
  These hypotheses do not establish that a physical truth belongs to the model.
- Root's Lean diagnostic uses hypothetical separating center2/5 and heldout center3/10.
  Worlds(6/25,4/5,4/25) and(4/25,4/5,6/25) each have a safe correction for all rho, but their
  safe-action intervals are separated by1/200. Both fit those observations at the original
  heldout error1/40, even with perfect separating precision. An extra half-leakage readout
  with error strictly below1/50 separates this pair only; it need not resolve the full set.
- Exact parametric precision thresholds and failure examples were independently checked by
  dual inequalities and feasible witnesses, without trusting producer vertex enumeration.
  The epsilon-family is ordinary exact mathematics, not itself a Lean theorem.

The independent critic replayed original certificates, all five Lean files, exact action and
precision checks, decision-coordinate supports and changed-readout pairs. Mutations of
coverage, bounds, witnesses, actions, summaries and a false Lean observation equality are
rejected. Accepted Lean declarations use only permitted standard axioms (generic logical
ones need none). The deliberately false Lean negative control fails and is excluded.
No solver-only output is promoted to proof. Root's initial compile-path mistake was corrected;
its failed log is preserved. Original sources and approved Challenge files were not edited.

## PM decision, missing assumptions and next action

GO after all60 initial reviews: one30-minute block builds an isolated proof-producing adapter
from joint polyhedral endpoint certificates to the four decision supports. Compare against
an exact joint oracle on at least20 predeclared heldout/calibration perturbations; test omitted
branches, inconsistent observations, stale model bindings and inappropriate reuse for updates.
The adapter must preserve the full joint relation for evidence and a nonempty guard for action.
Success means fewer decision constraints with identical decisions and independently checked
certificates, not a stronger physical claim. Then rank renewal by new evidence.

Physical application remains HOLD pending a justified phase/error/transfer/intervention and
actuator model connecting these static quantities to actual motion and safe termination.
No quadrature bound, stopping guarantee, hardware validation, novel attribution method or
publication claim follows. Prior-art links and access limits are in pm_analysis.md.
