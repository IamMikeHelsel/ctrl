# R01 domain research: authoritative intent is a contract, not a denoiser

AI-written by the domain role, inherited root model; exact identifier unavailable.
Owned artifacts are isolated research files. No original theorem, approved Challenge,
robot interface, or task specification was edited.

## Binding to the original work

Question: what authoritative task information is necessary to distinguish a genuine
small move from noisy observations of a hold without silently suppressing intended motion?
Read sources under
`/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/`:

- `intent-contract-07/analyst/report.md` and `motor-control-addendum.md`.
- `task-contract-08/builder/report.txt`, `TaskContract.lean`, and the
  `deadline_from_latency` lemma in `IsolatedHistory.lean`.

The same numeric 1 mm observation history is compatible with hold-at-zero and a true
1 mm move. With 0.2 mm tolerance the target bands are disjoint. This is prior work,
not a new discovery here. A filtering improvement cannot identify which hidden task
was intended from identical information. A deadband instead adds amplitude separation;
persistence adds temporal separation. Neither resolves the original identical-history case.

The existing `checked_isolated_task` already proves an isolated authoritative revision,
including exact guard acceptance and physical position bounds. It retains all old events,
requires their reference tails complete by issue time, binds the old final reference to a,
appends a new event with delta g-a, and requires execution time tau plus 4h no later than D.
It assumes the actual trajectory equations, rate/disturbance/budget and original time-zero
tracking cube. It does not reset state. The deadline corollary assumes bounded commit and
queue delays; its algebra does not verify clocks or transport. It does not prove physical
rest, mid-move replacement, task classification, authority routing or epoch selection.
We inspected the statements; we did not rerun the historical proof closure in this session.

## Three different transfers and their limits

1. **Typed authority versus estimation.** Map task revisions to commands and observations
   to state-estimation evidence. Preserve task identity independently of noisy samples.
   Breaks if the authority labels a wrong task, its coordinate frame is misunderstood, or
   its message has not arrived. The smallest practical distinction in this source is KEEP
   versus REVISE plus the revised acceptable goal, deadline and validity horizon. This is
   not a universal minimum bit count; overlapping task obligations can require less.
2. **Distributed command identity.** Map revision epoch to a durable ordered command ID,
   immutable payload to operation identity, and duplicates to idempotent acknowledgments.
   Preserve the accepted task against stale/repeated delivery. Breaks on authority/session
   confusion, lost durable state, conflicting payloads or an unbounded delivery gap. A
   receipt acknowledgment is not admission; admission is not physical task completion.
3. **Proof-carrying admission barrier.** Treat the source's completed-reference-tail fact
   as a token required before the next isolated revision. This deliberately rejects busy
   requests rather than pretending the old isolated theorem covers replacement. Reference
   tail completion is weaker than physical rest. A rejected request remains a failed
   request; latest-wins supersession needs explicit task authorization and a new theorem.

## Exact finite experiment

`domain_protocol.py` enumerates all 9,331 traces of length 0 through 5 over six events,
44,790 checked transitions. Alphabet: one advisory sample, two conflicting version-1
revisions, one version-2 revision, one wrong-session revision, and a trusted internal
`oracle_complete_tail` event. Exact integer goals are in micrometres. Every assertion passed.
`domain_protocol_results.json` records scope, examples and assumptions.

Invariants: accepted versions strictly increase; advisory/duplicate/conflict/wrong-session
messages do not mutate the committed task; a busy receiver cannot accept another revision;
stale revisions cannot roll back the committed goal; only the trusted reference-tail oracle
records a finished reference tail. Full immutable payload is simplified to the goal in this
fixture; deadline, validity horizon, frame, units and retained-history digest are not modelled.
The installed session and genuine authority are assumptions. The ledger is retained without
bound over the finite run. Protocol acceptance does not run the plant guard or claim its
acceptance theorem. There is no physical task-completion status in the final fixture.

Useful failures:

- Last-arrival-wins accepts version-2 hold then rolls back to a delayed version-1 move.
- Erasing the durable watermark permits stale version-1 replay after a version-2 hold.
- A new revision issued but not delivered leaves exactly the same receiver history as no
  new revision. Version numbers cannot supply missing authoritative information.
- Busy rejection persists on duplicate retry; resubmission needs a new ID and genuine
  admission, not a rewritten old operation or a claim that a move happened.

The critic found the first prototype's event name `complete` looked like an unauthenticated
packet and unknown event kinds fell through as revisions. The first draft's semantics are
preserved in `domain_protocol_first_draft.py` (reconstructed from the first executed draft,
with formatting/import/zip lint fixes). The final version names and documents completion as
an internal oracle, stores `reference_tails_done`, and raises on unknown kinds. A delayed
completion *packet* is not such an oracle: any implementation needs task/session/history
binding and a true current-tail check. Merely attaching the right ID does not establish the
predicate. This experiment exposes a missing bridge, not a bug in existing robot software.

## Small kernel proof and precise scope

`domain_monotone.lean` proves five properties of an explicit abstract reducer: observations
preserve state; watermark does not decrease for one event or any finite trace; busy revisions
preserve the goal; stale revisions preserve the goal. `domain_monotone_compile.log` records
successful compilation: either no axioms or `propext` only. The first missing-import failure
is retained separately. This is an arbitrary-trace theorem for that reducer, not a proof of
Python refinement, delivery, replay durability across restart, cryptographic authentication,
physical feasibility, task completion, or the original full plant theorem.

## What information is actually needed

For incompatible obligations, task-discriminating information must reach the decision maker
before it must commit to incompatible behavior. A trusted flag that has not arrived is not
available information. A guarantee conditional on authority cannot become unconditional by
using a better filter. In this particular source a workable sufficient interface includes:

- An authoritative initialized goal and distinction between observations and revisions.
- A revised target/acceptable set, tolerance, transition permission, deadline and validity
  horizon, interpreted in a common frame and time model.
- Command identity and immutable payload; explicit stale/conflict/busy rejection, retry and
  supersession semantics; durable fencing across restarts or a fresh trusted handshake.
- Bounded delivery/commit/queue delay when a fixed deadline is claimed, plus an actual
  admission check for tau + 4h <= D and the source's full-history completion/guard premises.

These are sufficient design ingredients for this route, not a claim that every conceivable
system must use epochs, digital packets or these precise fields. The genuine necessity is
separating information for incompatible tasks and timely access to it. Rejected motion must
be surfaced as rejection; it cannot be counted as successful hold or completed motion.

## Primary-source cross-check and novelty

[Lamport, Time, Clocks, and the Ordering of Events in a Distributed System (1978)](https://lamport.azurewebsites.net/pubs/time-clocks.pdf) distinguishes causal/logical ordering
from physical clocks. Logical command ordering alone does not establish a real-time deadline.
[Birrell and Nelson, Implementing Remote Procedure Calls (1984)](https://www.cs.cornell.edu/courses/cs614/2004sp/papers/BN84.pdf) uses call identity and sequence
information to control duplicate execution.
[Ongaro and Ousterhout, In Search of an Understandable Consensus Algorithm, section 8](https://raft.github.io/raft.pdf) discusses client serial numbers and retaining prior responses
for retries. These primary sources support borrowed protocol mechanisms; none proves this
robot task's safety or implies that a consensus implementation is required. No novelty claim.

## Domain recommendation

GO for a bounded contract-to-protocol bridge; NO-GO for inferring incompatible hidden intent
from the unchanged measurement stream. Next discriminating test: explicit issued/received/
admitted/rejected/reference-tail-finished/task-satisfied state machine with authenticated
session/version/payload/history identity, durable restart rules, and bounded clock/transport
assumptions. Compose an admitted isolated revision with `checked_isolated_task`, without
identifying reference-tail completion with physical rest or extending to mid-move replans.
First adversarial cases: delayed completion from an earlier task, restart replay, same-ID
payload conflict, rejected busy retry, undelivered revision and false rest declaration.

Quality estimate: faithfulness 4/4, reproducibility 4/4, discriminatory value 3/4,
critique 4/4, actionability 4/4 = 19/20 (95%). Subjective confidence: high in the finite
results and source-scope boundary, moderate that this exact interface is the best next design.
PM owns the final decision and campaign grade.

## Additional discrimination: intent success versus observable motion

The original bound gives directed progress at least |delta|F-R, hence strictly
positive progress only when |delta|F>R. Authoritative intent therefore does not
by itself certify arbitrarily small physical motion under the existing tolerance.
`domain_small_motion.lean` proves that for 0<=delta<=R and every interpolation
parameter u in [0,1], a constant hold at zero stays inside the position tube around
delta*u. The numerical instance is a 0.1 mm reference move with a 0.2 mm tube.
This is a countermodel to extracting positive motion from the tube condition alone,
not a plant trajectory construction or a counterexample to the original ODE theorem.
To require actual small motion, the task must say so (e.g. positive displacement with
a lower bound), and a stronger tracking/progress certificate must establish it.
Reaching a target tolerance already containing the old pose is a weaker obligation.
