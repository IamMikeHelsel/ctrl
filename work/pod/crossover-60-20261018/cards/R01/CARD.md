# R01: Task intent versus measurement ambiguity

**PM: GO for a bounded authority-to-history certificate experiment after all60 initial reviews.**
Full composition with the existing physical theorem remains HOLD at a named issue-time
premise. Quality19/20(95%): faithfulness4, reproducibility4, discriminatory value4,
independent critique4, actionability3. Subjective confidence is high in the scoped exact
counterexamples; implementation utility and physical applicability are untested.

AI-written by root PM plus domain, inventor and independent critic. All three workers
used the inherited root model; exact runtime identifier unavailable. No alternative model
family or Spark inference contributed to this session. No hardware commands occurred.

## Frozen question and provenance

What authoritative task information is necessary to distinguish a true small move from
noisy observations of a hold without silently suppressing intended motion?
Wildcard R01, source-linked prior investigation:

- `/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/intent-contract-07/analyst/report.md`
- Same analyst directory: `motor-control-addendum.md`.
- `/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/task-contract-08/builder/report.txt`

The earlier work already establishes packet-history indistinguishability and proves an
isolated authoritative-goal position contract. Its actual `checked_isolated_task` theorem
retains the complete reference history, assumes the old tail is complete at issue time,
checks the new guard, and composes with physical ODE/tracking premises without resetting
state. Authority, routing, delivery, clocks and actual physical rest remain outside it.
We did not reclassify that prior theorem as new work or edit its source. The full old dependency closure was not freshly rebuilt in this session; its declaration and recorded verification were inspected.

## Answer: information is task-relative

An observation history defines a set of possible tasks. Additional authoritative information
must separate tasks whose obligations have no common admissible behavior. It need not
identify distinctions that the task permits us to ignore. A hold/revise bit alone is not
sufficient when multiple incompatible move targets share the same observations. The task
must also say whether success means arrival within tolerance or actual directed progress.
Target precision, deadlines, task lifetime and transition permissions must support the
particular guarantee claimed. Transport identifiers preserve that meaning; they cannot
establish that an asserted task is the true task.

## Creative transfers and their failure boundaries

1. **Information theory and compatible task classes.** Partition possible tasks by a
   common valid behavior. This preserves the decision requirement rather than recovering
   all hidden intent. For scalar intervals, pairwise compatibility suffices for a common
   point; it need not suffice for higher-dimensional goals or trajectory sets.
2. **Distributed transactions and immutable command identity.** Bind authoritative
   request, compilation and reference-history append to one identity and exact payload.
   Repeated delivery should return the existing receipt. Ordering does not imply timely
   delivery, truthful authority, physical completion or safe cancellation.
3. **Refinement and proof-carrying admission.** A certificate must instantiate the actual
   old theorem's premises, including complete old tail at issue, guard, deadline and plant
   assumptions. A self-consistent event list is not automatically the authorized task.
4. **Unexpected error-correcting-code view.** Semantic distinctions and corruption
   protection consume different information. A bounded one-bit-error channel can be tested
   as a coding problem, but integrity cannot repair a truthful-looking wrong intent label.
   Motor-control minimal intervention remains a design analogy, not an inference of intent
   or a diagnosis of tremor.

## Tests that change the next step

**Authority content.** Three possible goals0,0.5,1mm can share the observed1mm packet and
have disjoint0.2mm success bands. All8 binary encodings fail;6 ternary encodings succeed in
this finite endpoint model. A declared fixed-word, one-bit-correcting extension needs5bits
for three codewords. This is a small coding fixture, not a universal bandwidth minimum.

**Arrival may permit no motion.** For a0.1mm goal with0.2mm tolerance, staying at0 already
satisfies arrival. Two Lean lemmas show a constant hold lies inside every interpolated
position tube when0≤delta≤R. This is a countermodel to inference from the tube alone,
not an admissible-ODE trajectory counterexample. Actual directed movement needs an
explicit progress obligation and a sufficiently strong physical bound.

**No target-quantization margin in the current abstraction.** With epsilon=R=0.2mm,
requiring |q+e-g|≤R for every e∈[-R,R] forces q=g. Lean proves this and injectivity of any
real-goal encoder/decoder satisfying that universal requirement. A1micrometre target
error can break the inherited tolerance bound. We did not change R or tolerance; the
result concerns the full-tube abstraction, not attainability of every endpoint error.

**Task identity must reach the append operation.** Replaying a compiled1mm increment at
0.22s and0.23s gives a2mm final reference. Its exact peak jerk is77/160m/s³, below7.5;
a simple conservative bound is0.5m/s³. Lean evaluates the original four-box formula and
proves that any position in its0.2mm tracking tube misses the intended1mm goal by at
least0.8mm. This is replay after compilation. Recompiling an absolute goal against the
already updated goal can instead produce a zero increment. No existing pipeline defect
or new physical trajectory is asserted.

**Protocol experiment.** Domain enumerated9,331 traces and44,790 transitions. Accepted
versions increase; observations and duplicates do not change committed task identity;
busy/stale/conflicting requests remain explicit failures. A five-lemma Lean reducer proves
abstract finite-trace invariants, not refinement of the Python receiver. The initial draft
allowed an unbound completion packet and unknown-kind fallthrough. Critique forced an
explicit trusted current-tail oracle and rejection of unknown kinds; the draft survives
as negative evidence. Reference-tail completion is not task completion or physical rest.

**Append and authority certificates.** Root's exact finite prototype binds prior history,
revision, goal, deadline, width and compiled event. Mutation tests reject stale prefixes,
changed payloads, wrong increments and pending tails. Independent review caught and
corrected two unit literals before promotion. A wrapper additionally checks a separately
supplied authoritative receipt, causal admission and the frozen isolated jerk bound.
Late identical retries return the old receipt without a second effect. A false authoritative
receipt remains trusted; the model does not infer task truth. No hashes or collision
assumptions are needed because the prototype compares exact history tuples.

**Remaining concrete bridge failure.** The old event starts0.22s and ends1.02s. A new
request issued/admitted0.5s with execution1.5s passes the prototype's execution-order test,
but violates the original theorem's `CompleteBy(h,s,old)` at issue s. The receipt currently
omits issue time. Scheduling later does not repair that theorem binding. This precise
failure, plus required physical premises, blocks end-to-end theorem promotion.

**Information must arrive in time.** Three root Lean lemmas show, under a separately
stated finite-speed toy assumption, delta−2epsilon≤speed*(deadline−arrival) is necessary
when the pre-information state must satisfy a hold. The1mm,0.2mm,1mm/s example cannot
succeed at1s if distinguishing information arrives at0.5s. This optimistic necessary
bound is not a speed bound imported from the original FIR plant.

**Higher-dimensional negative control.** Three unit disks centred at(0,0),(2,0),(1,3/2)
have pairwise intersections but no common point, kernel-checked. It is a declared2D
extension illustrating why a pairwise conflict graph can miss a joint obligation.

## Evidence and independent critique

Seventeen isolated Lean declarations compile with only permitted axioms, with formula
binding and independent replays. Exact finite-state, rational-reference, encoding and
mutation experiments are separately recorded. The critic reproduced producer artifacts,
rejected corrupted evidence, exposed draft protocol/unit/binding errors and preserved
failed versions. See `critic.md`, `inventor_verification.json` and `pm_lean_replay.json`.
No solver status, observation classifier, new closed-loop theorem, real robot result,
complete protocol implementation or novelty claim is accepted.

Primary checks covered [Birrell–Nelson's RPC identifiers and replay semantics](https://www.cl.cam.ac.uk/teaching/0708/DigiCommI/birrell1984rpc.pdf),
[Lamport's distinction between ordering and physical clocks](https://lamport.azurewebsites.net/pubs/time-clocks.pdf),
and [Todorov–Jordan's task-dependent feedback model](https://people.eecs.berkeley.edu/~jordan/papers/coordination.pdf).
These are established mechanisms; selected passages were checked, not a systematic review.

## PM next action and gate

After all60 initial reviews, spend30minutes on an isolated typed receipt-to-admission adapter
that carries issue time and binds the full task payload and retained history to the actual
`checked_isolated_task` premises. Predeclare at least20 traces covering duplicate compiled
events, stale sessions, lost durable state, wrong goal, late retry, busy rejection, old tail
unfinished at issue, wrong clock, unsafe jerk and false completion. Use a proof of admission
or an explicit rejection; never report a rejected task as completed. Demonstrate one exact
accepted trace and independently rejected mutations before extending scope.

GO for this bounded experiment. HOLD full theorem composition, mid-motion replacement,
trusted runtime clocks/authority, physical rest and hardware. NO-GO for universally inferring
incompatible hidden intent from unchanged numeric observations. Timing and resource evidence
are in campaign state/activity/resources; ten minutes reviewed is not ten minutes proved.
