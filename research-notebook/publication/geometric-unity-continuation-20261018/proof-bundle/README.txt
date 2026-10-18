GU algebra proof bundle

Final acceptance: PASS. The integrated run rebuilt and separately replayed 48
modules (38 mathematical modules and ten reviewer modules), rejected 20 false
clients, and audited all 723 owned declarations. See acceptance-review.json.

Purpose
This portable bundle preserves and rechecks an existing formal algebra baseline.
It does not establish Geometric Unity as a physical theory. The 25 files in
source/ are byte-identical to accepted builder-05. Reviewer controls are copied
from critic-05. The original workspace and frozen sources are unchanged.

Pins
Lean: leanprover/lean4:v4.35.0, compiler commit
eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679.
lake-manifest.json pins all transitive dependencies. No local dependency patch
is applied. replay.py checks every dependency revision and clean working tree.

Replay with existing dependency products
  python3 replay.py --dependency-project /path/to/lean-controls --lake /path/to/lake
Set ELAN_HOME first if the existing toolchain uses a nondefault elan home.
A dependency project must have the exact manifest pins and compiled dependencies.
Only public dependency products are reused. The dependency project's own build
products and earlier local proof products are excluded from LEAN_PATH.

Replay on a new machine with elan and Python 3 installed
  cd proof-bundle
  lake update
  lake exe cache get
  python3 replay.py
The pinned Mathlib revision fixes its dependency declarations. Verify that update
retains the supplied package revisions; replay.py checks the checkout and manifest.
These bootstrap commands are documented, but a network-clean install has not been
performed in this run. Local fresh rebuild and replay are recorded in logs/.

Outputs and trust
Every invocation creates a fresh .replay/<timestamp>/ with local .lean and .olean
files and logs/<timestamp>/ with separate compilation and leanchecker outputs.
latest-result.json records the most recent successful run. A compiler success is
not presented as a separate replay: both phases must independently return zero.
leanchecker replays terms in a separate process with Lean's kernel; it is not a
second independently implemented proof kernel. Compiler, dependency products,
operating system and hardware remain in the trust base.

The final audit examines every declaration owned by all 25 source modules and
both reviewer modules, including private helpers. It rejects owned axioms, unsafe
declarations, sorryAx, and any axiom outside propext, Classical.choice, Quot.sound.
Nine false clients must fail through unsolved mathematical goals, without import,
syntax or type failures. CounterWitnesses proves their exact negations.

Independent arithmetic cross-check
  python3 integer_oracle.py
This inherited reviewer oracle constructs exterior operators from sorted tuples.
It rechecks 128 basis actions and 1,507,328 matrix-entry equalities, plus 32 complex
integer pairings. It supplements Lean. It neither replaces proofs nor tests physics.

Storage
Ship source/, controls/, provenance/, pinned Lake files, scripts, docs and logs.
Exclude .replay/ and .lake/. These caches are rebuildable and are not source.
SHA256SUMS covers the portable deliverables at the recorded checkpoint.

Integrated additions
accepted/ contains thirteen frozen new modules. accepted-origins.json maps each to
its original working source and SHA256. accepted-controls/ contains eight new
reviewer modules and eleven false clients. accepted-hashes.json fixes those files.
Run the complete proof suite with the same CLI arguments as replay.py:
  python3 integrated_replay.py --dependency-project /path/to/project --lake /path/to/lake
On a new machine with the dependencies prepared in this folder:
  python3 integrated_replay.py
This builds 48 modules from fresh copied source in topological order, then
separately replays each with leanchecker, runs 20 false clients and audits every
owned declaration. latest-integrated-result.json is written only on success.
The complete integrated evidence is distinct from the earlier independent gates.

Inventory hardening and recorded acceptance
inventory_check.py verifies the exact 70 proof-critical files, their accepted
baseline provenance, the 48 positive modules, all 20 false clients, and the
complete generated audit template. It remains effective under optimized Python.
Twelve mutation checks (three valid accepts, nine targeted rejects) are recorded
in provenance/inventory-mutation-results.json.

Inventory hardening was added while the final proof replay was already running.
That replay's exact invoked-runner.py and hash are preserved in its log folder.
The hardened future runner calls the inventory gate before and after execution
and rejects Python optimization. It was not rerun wholesale for this packaging
change. The independently run additive inventory and outcome checks certify the
same complete source/control inputs and all recorded verification outcomes.
Run `python3 acceptance_review.py` after an integrated replay to regenerate that
combined acceptance record. acceptance-review.json is the concise final gate.
