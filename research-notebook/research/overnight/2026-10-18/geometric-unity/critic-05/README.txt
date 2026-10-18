Independent review of the frozen actual split-signature gate

The builder sources remain untouched. This folder owns only review code, copied
source, client probes, logs and reports. Root owns repository synchronization.

Read REPORT.txt for the decision, statement-review.txt for the mathematical map,
and NEXT-GATE.txt for source-definition blockers and the stop recommendation.

Reproduction from this workspace
- review.py verifies the frozen builder and ten prior manifests, checks inherited
  source identity, derives a local import order, builds all 25 local sources in a
  fresh output path, and runs the separate leanchecker on each module.
- client_review.py compiles 22 reviewer client theorems and rejects 9 false clients.
  It requires unsolved mathematical goals and rejects infrastructure failures.
- counter_review.py proves the negation of each of those 9 false claims and audits
  every local declaration in all 25 sources plus both reviewer client modules.
- integer_oracle.py independently constructs the wedge matrices from insertion
  permutations and contraction positions. It uses standard-library integer
  arithmetic and imports no builder Python code or result data.

Run review.py first, then client_review.py, then counter_review.py. The output
path must be fresh. Preserve earlier evidence rather than overwrite it. In this
record the client checks ran after all 25 source builds had passed while the
separate source-module checker replays continued. All jobs finished before freeze.
The external pinned public dependency cache is reused. No builder cache, root
project build cache or older local compiled module is in LEAN_PATH.

The cache directory holds generated compiler products and is excluded from the
frozen review manifest. The copied source, logs, environment, clients and scripts
are included. The manifest excludes itself. Compiler binaries, pinned dependency
products and the hardware remain in the trust boundary. leanchecker is a separate
replay process, not a second implementation of the Lean kernel.

No Git, manuscript, shared-state, submission, external-message or billing action
was performed by this reviewer. No new subagent or paid API was used.
