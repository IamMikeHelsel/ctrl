# S12 domain review — uncertainty-preserving decisions

AI-written role work; inherited root model, exact runtime identifier unavailable.
PM owns session timing and final gate. All new files stay in this card. Original artifacts,
approved challenges and the active source-attribution demonstration were not edited.

## Exact question and recovered model

Can a decision remain sound while source attribution is nonidentifiable and measurements
contain duplicated shared information? Yes as a conditional robust-decision principle:
retain the actual joint worlds compatible with justified bounds, reject an empty set, and
accept only an action safe in every retained world. This principle does not establish that
the physical truth actually belongs to that set or that a static response bound is a dynamic
safety guarantee.

Sources inspected:

- `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/source-attribution/challenge.txt`
- `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/adjacency-review/coupled-measurements.txt`
- The same source-attribution directory's `model.json` and `check.py`; original `check.py`
  was run afresh through uv against its pinned artifacts.

The demonstration is static, real, scalar and signed-phase. Variables are wheel w,
drivetrain d, and q=lambda*d, with w,d in [-2,2], lambda in [1/5,3/10]. Wheel gain is
assumed exactly1. Baseline is w+d in [9/10,11/10]; trial adds a known1/2 wheel offset
and otherwise repeats the same constraint. The separating observation is w+q in[3/5,13/20].
Heldout uses w+q/2 in[43/80,47/80], expressly not as an identification update.
Correction c changes w alone; bounds are |w+c|≤1/8 and |w+c+rho*d|≤3/4 for every
rho in[0,1]. Common sources, phase, support and leakage across conditions are hypotheses.

Fresh original checker result:56 endpoint certificates,1 infeasibility certificate,
8 action evaluations pass, with complete declared stage/branch/objective/action coverage.
Its hash pins the model, and its checker rejects Python-O. The same baseline, duplicate
and selected trial leave wheel range[-11/10,2]. The separating observation narrows it to
[27/70,47/80]. Action-1/2 passes; -1 fails. This is already an exact rational illustration,
not an open numerical claim and not a new source-separation method.

## What the original heldout check does and does not prove

After separation, only one convex sign branch survives. Its scalar image is an interval;
intersection with the heldout interval therefore implies existential compatibility in
that particular model. The source checker explicitly checks this branch condition. No
existing hull-compatibility bug was found. Compatibility is not universal prediction,
truth validation, or dynamic safety. The strongest unresolved obligation is physically
justified bounds and unchanged transfer paths under intervention, including missing
quadrature and transients if a robot claim is intended.

An outer approximation is safe for universal upper-bound certification, although it can
reject useful actions. It is unsafe to use intersection with that outer approximation as
proof that the exact model has a compatible world. This quantifier difference is the
useful abstract-interpretation crossover: preserve containment for universal reasoning,
and preserve a real shared witness for existential reasoning.

## New exact disconnected negative control — explicitly changed model

This is a baseline-stage extension, not the frozen separated demonstration. Changes are:

1. Add a declared disjunctive amplitude prior 1/2≤|d|≤1.
2. Keep the baseline and redundant trial, but do NOT impose the original separating row.
3. Keep heldout row(1,0,1/2), but replace its observed interval by[19/20,21/20].

Original w bounds, lambda bounds, common q=lambda*d and signed interpretation remain.
The added minimum amplitude would need independent justification for any real use; here
it deliberately produces two modes to test branch preservation.

For d≥1/2, combine baseline upper bound, q≤3d/10, and -d≤-1/2 with nonnegative weights
1,1/2,17/20. This proves w+q/2≤27/40. For d≤-1/2, combine the negated baseline lower
bound, q≥3d/10, and d≤-1/2 with the same weights; it proves w+q/2≥53/40.
Both branches are nonempty: (w,d,q,lambda)=(3/5,1/2,3/20,3/10) and
(7/5,-1/2,-3/20,3/10). Their predictions27/40 and53/40 bracket the new observation,
so the prediction hull intersects it, while the exact union does not.

`domain_gap_exact.py` checks full witness priors, both baseline/trial readings, the
shared leakage equality and rational dual combinations. It writes
`domain_gap_exact_results.json`. No solver or vertex-enumeration completeness is trusted.
It rejects Python-O. The relevant inequalities are separately kernel checked in
`domain_gap.lean`; the Lean witness arithmetic plus Python full-feasibility check should
not be misreported as a fully formalized configurable polyhedral-model checker.

The critic correctly identified two binding ambiguities in the initial description:
the original separating row is absent, and the heldout value changed. The file header
and this report now name both changes. This negative control demonstrates a general
failure mode, not a defect in the original accepted result.

## Generic machine-checked contract

`domain_guarded.lean` proves seven statements: true-world preservation under a sound
measurement update; duplicate predicate idempotence; accepted action soundness for a
retained truth; rejection of an empty retained set; conservative universal reasoning
from an outer set; acceptance after checking every branch plus nonemptiness; and heldout
compatibility requiring one shared world in one branch. All seven report no axioms.
`domain_gap.lean` compiles its four rational inequality/arithmetic theorems with only
propext, Classical.choice and Quot.sound.

These are isolated new research statements, not solutions bound to approved Challenges.
Their hypotheses expose rather than solve the physical containment problem. Quantifying
over every Branch does not certify that an implementation enumerates every required
branch or preserves the pinned model; runtime branch coverage and provenance still need
an independently checked bridge. Duplicate idempotence refers to the same predicate,
not a license to assert statistically independent errors or discard a distinct transfer
path. No covariance-to-deterministic-bound conversion is assumed.

Reproduction:

    uv run python work/pod/crossover-60-20261018/cards/S12/domain_gap_exact.py
    cd lean
    lake env lean ../work/pod/crossover-60-20261018/cards/S12/domain_guarded.lean
    lake env lean ../work/pod/crossover-60-20261018/cards/S12/domain_gap.lean

Scoped Ruff check and format pass for the new Python script. Original certificate checker
passes. The gap compile log is retained. These are local proof/checker results, not physical
validation or publication novelty assessments.

## Decision advice and next discriminating test

GO for a bounded checker extension/regression exercise: use exact branchwise joint
heldout feasibility, explicit nonemptiness and signed certificates; test that omitting a
branch, replacing the union by its hull, or changing the model hash is rejected. HOLD any
robot-safety interpretation pending a coupled dynamic model and justified measurement,
phase, intervention and actuator bounds. No unique attribution is logically required
for a universally safe static action; lack of identifiability can instead force abstention.

Role quality estimate: faithfulness4/4, reproducibility4/4, discriminatory value3/4,
critique4/4, actionability3/4 =18/20 (90%). This grades the bounded analysis, not novelty
or physical safety. Subjective confidence: high for logical/rational claims; no quantified
confidence in physical transfer. PM owns the final campaign grade and decision.

## Original-model numeric bridge added during PM review

The inventor identified the complete robust static correction interval
[-143/280,-37/80]. `domain_original_action.lean` now checks the corresponding arithmetic
over real-valued worlds using the ORIGINAL baseline and separating observations, original
leakage bounds and exact q=lambda*d. No amplitude-floor prior or changed heldout row enters
this file.

First, baseline minus separating constraints imply d≥0; hence d/5≤q≤3d/10. Linear
combinations give27/70≤w≤47/80. For every correction in the stated interval, the wheel
residual lies in[-1/8,1/8]. The mixed response is a convex combination of w+correction
and w+d+correction, both inside[-3/4,3/4], so its limit holds for every rho∈[0,1].
The formal sufficient theorem quantifies over arbitrary real rho with those bounds.
It does not need the original w,d prior boxes, so it holds on a larger set and therefore
on the original set.

Necessity follows from two actual original-model worlds:

- w=27/70,d=5/7,q=3/14,lambda=3/10;
- w=47/80,d=5/16,q=1/16,lambda=1/5.

Their original prior boxes, leakage equations and baseline/separating readings are checked
by the endpoint theorem. Requiring the wheel limit at both endpoints forces correction
in[-143/280,-37/80]. Thus the paired sufficient and necessary theorems establish the
complete static action interval; this is stronger than testing only the two originally
predeclared actions, while reusing the original source's already certified wheel bounds.
This interval remains valid despite nonunique source attribution.

Four numeric theorems compile and audit with only propext, Classical.choice and Quot.sound.
The first attempt failed because the Real.Basic import was missing; the failed diagnostic
log is retained as `domain_original_action_compile_attempt1.log`. Adding that import and
setting autoImplicit=false fixed the setup, and the successful audit is recorded in
`domain_original_action_compile.log`. No proof hole or changed constraint was used.
PM and critic were asked to independently inspect the statement binding and recompile.
The new theorem is still a conditional static scalar result, not a dynamic-safety bridge,
not an approved-Challenge solution, and not a claim of novel attribution theory.

This original-model result is the stronger continuation target: bind the numeric certificate
adapter and complete action interval to frozen model provenance, then independently validate
new measurements before considering any physical intervention. The disconnected extension
remains useful as a negative-control fixture and should not displace the original-model result.

## Decision-coordinate compression versus joint evidence

The inventor proposed storing the marginal box in coordinates(w,b), where b=w+d,
for this frozen decision rule. The relevant identity is

    w+c+rho*d = (1-rho)(w+c)+rho(b+c).

For rho∈[0,1], its absolute bound is equivalent to the two endpoint absolute bounds.
Thus only the individual ranges of w and b enter the wheel and mixed decision objectives.
`domain_decision_box.lean` proves a general losslessness statement: if the exact world
set lies within a coordinate box and attains every marginal endpoint, universal bounds
on these endpoint objectives hold over the exact set if and only if they hold over the
whole box. It also checks the coordinate identity, convex endpoint equivalence and an
interval absolute-bound lemma. The original certificate format already provides both
valid dual bounds and feasible endpoint witnesses; those are the ingredients needed
for a subsequent model-to-theorem adapter. A mere conservative interval bound guarantees
soundness, but not losslessness without the attainability evidence.

This decision representation is NOT a replacement for joint measurement feasibility.
The point(w,b)=(27/70,9/10) lies in the original decision box, but setting d=b-w forces
d=18/35. Shared leakage then gives q≤27/175, so w+q≤27/50<3/5, violating the original
separating observation. The incompatibility is kernel checked in the same file. This is
a hypothetical joint readout/consistency query for(w,b), not the original heldout scalar
observation and not a claim that the wheel component is directly measurable.

All six theorems compile with only propext, Classical.choice and Quot.sound. A failed
intermediate compile of the added coordinate identity required importing the Ring tactic;
its log is retained, and the final successful audit contains no proof-hole axiom. Final
source and log were sent to the independent critic. Unlike the earlier disconnected
negative control, this incompatible box point uses the original separating constraint
without changing its interval or adding an amplitude floor.

Practical continuation: retain the full joint model for identification and heldout
compatibility, and generate a provenance-bound decision representation for exactly the
frozen acceptance objectives. Changing response objectives, operating range or observation
queries requires rechecking the abstraction theorem; the losslessness claim is not a
general covariance, posterior, or physical-state compression result.
