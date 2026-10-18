BIND A CHECKED PLAN TO THE STATE AT EXECUTION

Read CLAIMS.txt for the
exact theorem, examples and boundary. This is a builder artifact pending a fresh
independent critic. Root owns repository synchronization and paper integration.

Files
FutureCommit.lean: structures, executable rule and general real-reference proof.
FutureCommitFixtures.lean: moving acceptance, rejections and lost-contract proofs.
protocol.txt / protocol-freeze.json: fixed test design before fixtures.
PROTOCOL-ERRATA.txt: correction to the handwritten heading's clock label.
source-freeze.json / input-bindings.json: proof/replay and inherited source pins.
verify.py: fresh-source build, all-local declaration audit, separate kernel replay,
  and deliberately false clients. Prior build caches are excluded from its path.
exact_scenarios.py / exact-event-log.json: separate Fraction arithmetic check.
client.py / clients/: small exact-rational input interface. JSON parsing is not
  formally verified. Each generated decision and consequence is kernel checked.
attempt-*/: preserved failed development proofs and their diagnostics.

Verification
From this workspace, run python3 <this-folder>/verify.py in a new sibling copy
under the robot-motion folder, with .cache omitted. The driver locates the
workspace from that folder layout. Existing .cache/fresh is deliberately not
overwritten. Pinned Lean and
mathlib are supplied by the existing lean-controls dependency project. The
source-closure file records every local source and its exact hash. Fresh means
local proof sources are rebuilt; mathlib dependency products are reused.

After verification passes, check a rational scenario with:
python3 <this-folder>/client.py <this-folder>/clients/on-time.json <new-output-dir>

Every rational is a string such as "57/100"; decimal and executable text are
rejected. Versions are nonnegative JSON integers. The six supplied JSON clients
cover acceptance, late completion, changed history, replaced task, duplication
and an insufficient candidate deadline.
client.py first evaluates the Boolean to discover the result, then independently
asks Lean to prove that exact result with decide +kernel. The generated client
also derives the reference contract on acceptance or unchanged live state on
rejection. It invokes the separate kernel checker. The parser, input origin,
clock values and atomic state capture remain outside the formal proof boundary.
No numeric schema claim can identify the actual robot state by itself.

The .52/.57/.62 s example is an exact scenario with a positive time allowance.
It is not a measured execution-speed or hardware demonstration. No physical
trace or extra optimizer run was produced for this gate.

Concrete workspace example (the output directory must not already exist):
python3 research/overnight/2026-10-18/robot-motion/builder-05/client.py research/overnight/2026-10-18/robot-motion/builder-05/clients/on-time.json /tmp/ctrl-future-commit-example

This command assumes verify.py has already passed in this working folder. The
expanded publication bundle may provide a different portable dependency loader;
this small client deliberately uses the existing workspace pins and fresh gate.
