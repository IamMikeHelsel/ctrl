CHECKED MOTION REVIEW PACKAGE — version 2, 18 October 2026

Purpose
This package brings six reviewed proof components into one replay. It copies
63 local Lean modules without changing their source bytes. It covers exact
reference jerk/acceleration checks, a sufficient speed check, finite candidate
selection, completed-history removal, an equivalent acceleration checker,
a future commit rule, and a conditional scalar physical terminal theorem.
Read the accompanying independent review reports for each component's scope.
Final integration-review decisions are recorded separately; automated reviews
are not external human peer review.

Read the guarantees separately
The reference is the planned motion. An accepted future commit binds a proof to
the exact live history and task, including goal, limits and absolute deadline.
It leaves the earlier reference unchanged through execution. A failed check
retains the live plan. It does not complete the newly requested task.

Reference jerk and acceleration checks are exact. The speed check is sufficient:
it can reject a safe motion. A finite candidate list can miss feasible choices.
Removing completed tails preserves future reference jets and jerk/acceleration
decisions. No equivalent rewrite of the combined timed speed selector is claimed.

The physical result concerns one scalar plant and controller. Its response may
change between 80 and 120 per second; disturbance magnitude is at most 0.01 m/s². A supplied
classical trajectory and one initial transformed error cube are premises.
For the fixed FIR return, position tracking stays within 0.2 mm. Position is within
0.2mm of zero from 1.42 s; speed is at most 1 mm/s and acceleration at most 0.02 m/s²
from 3.42 s. These are residual bands, not exact rest. The theorem does not prove
the numerical experiment's 1.70 s physical deadline or cover a coupled robot.

Provisioning boundary
Use Python 3.9 or later and an already provisioned Lake project with the three
exact files in dependency-project/. Mathlib revision:
56a005855ea17e0b0958f73ec801ae140b0a1679.
Lean 4.35.0 compiler commit: eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
No third-party Python package, paid API or hosted runner is needed for replay.
Public dependency caches are reused. Local project caches are excluded.

First, replay the proofs
Run from any folder with your own absolute paths:
  python3 /path/to/package/replay.py \
    --dependency-project /path/to/pinned-project \
    --lake /path/to/lake \
    --elan-home /path/to/elan \
    --output /path/to/new-proof-replay

The output must not exist. The replay checks original source and reviewer
manifest bindings. It fixes the exact source roots, 22 kernel targets and 33
negative-control files in its code. It builds the 63 local modules from fresh
sources, audits all their declarations, separately replays the named kernels,
and requires the 33 false clients to fail for mathematical reasons. Missing
imports do not count as a successful negative test. It saves logs, source hashes,
compiled-object hashes and results.json. Failures remain available for review.

Then, check one rational request
  python3 /path/to/package/client.py \
    --input /path/to/package/examples/on-time.json \
    --replay-output /path/to/new-proof-replay \
    --output /path/to/new-client-result

Use the six examples to see one acceptance and rejections for late completion,
stale history, a superseded task, duplicate use and the tighter deadline.
The client snapshots the input bytes, rejects duplicate JSON keys, and writes
the exact generated Lean literals. Evaluation proposes a decision; Lean proves
that decision and its consequence, then leanchecker checks the generated module.
The output contains the input snapshot, readable Lean proof, logs and result.json.
Each output directory must be new and outside both the package and proof replay.

Input meaning
Rational values are strings such as "13/25" or "0". Decimal numbers and decimal
strings are rejected. Versions are nonnegative JSON integers; booleans are not
versions. All objects require exactly the keys shown in the examples.
The pending object carries its base, task, proposed execution, signed increment
and finite execution candidates. Live base, live task and timing are separate
input objects. Full structural equality is checked, not just version equality.

Completion includes all computation and verification. It must follow the request
and precede or equal commit. Commit plus the nonnegative dispatch allowance must
precede or equal the proposed execution. The on-time example declares request
0.52 s, completion/commit 0.57 s, dispatch 0.01 s and execution 0.62 s. These values are
formal inputs; they are not measured timing of this Python or Lean process.

Trust and limits
The parser, runtime clock, truthful timing inputs and atomic capture/update of
a controller's live state are outside the formal theorem. This is an offline
proof client, not a live executor. A sound checker can reject every request on
an overloaded system. It proves no progress rate, emergency stop or real-time
capacity. The fresh replay record and machine are trusted local evidence, not
an authenticated remote attestation. Hashes detect recorded changes; they are
not digital signatures. Compiler and dependency binaries remain trust boundaries.
The allowed proof axioms are propext, Classical.choice and Quot.sound.

This package does not reproduce the floating-point numerical comparison or
optimizer as a Lean proof. Those are separate, independently reviewed artifacts.
The stronger smooth comparison omits calculation latency. Reference bounds do
not become physical bounds without the model theorem's premises.
There was no hardware test, machine-safety rating, public release or submission.
Licensing, affiliation, venue and external human review remain owner decisions.

assemble.py and assembly-config.json describe workspace-side packaging. They
need the original workspace and are not needed to run portable replay.
parser-provenance.json records the copied literal generators and adapter changes.
The older 50-module package and every old failure remain in the repository.
