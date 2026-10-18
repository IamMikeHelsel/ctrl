REVIEWER PROOF PACKAGE — 18 October 2026

Purpose
This package copies 50 local Lean modules without changing their bytes. It joins
three independently accepted proof gates: conditional physical position arrival,
completed-history pruning, and the equivalent successor acceleration checker.
The copied review reports define each acceptance boundary. They are automated
independent reviews, not external human peer review.

What is proved
The scalar four-box reference has exact rational jerk and acceleration guards.
A finite candidate rule can delay or reject an execution time while preserving
its stated reference bounds. One concrete delayed-return task composes with the
declared scalar tracking ODE to prove position tracking and position arrival.
PhysicalArrival retains the physical trajectory from time zero. It does not
prove actual velocity, acceleration or rest at the endpoint.

HistoryPruning removes completed event tails and retains their position offset.
It preserves future reference position, velocity, acceleration and jerk, and
the jerk/acceleration guard decisions. It does not preserve past motion.

SuccessorGuard checks adjacent knot cells and has the same acceptance as the
earlier exact acceleration checker. This is a reference theorem. Saved runtime
measurements are separate evidence and are not included as a real-time claim.

Not included
No generic velocity admission result is claimed by this package. No claim here
extends the scalar model to a coupled arm, contact, payload, sampled hardware,
or a safety performance level. The 72-trace native comparison is a separate
numerical artifact. This package is not a new smoothing algorithm or evidence
of publication novelty. The known reversal-overlap failure appears in earlier
FIR trajectory literature.

Replay
Use Python 3.9 or later. The replay script has no third-party Python dependency.
Use an already provisioned Lake project with the exact three files shipped in
dependency-project/. Its mathlib checkout must be at
56a005855ea17e0b0958f73ec801ae140b0a1679. Lean is 4.35.0 at compiler commit
eb6cafb7290e8bd5f2937522d8d804f58f02bafc.

Run from any folder, substituting your own paths:
  python3 /path/to/this-package/replay.py \
    --dependency-project /path/to/pinned-project \
    --lake /path/to/lake \
    --elan-home /path/to/elan \
    --output /path/to/new-replay-output

Omit --elan-home if your configured elan home supplies the pinned compiler.
The output directory must not exist. Failure evidence is retained. A successful
run writes results.json, build logs and fresh local .olean files. These generated
files are evidence from your replay, not inputs shipped as proof sources.

The script checks source hashes against three frozen gate manifests, rather than
only a new package manifest. It checks review report bindings, compiles the full
local closure into an empty build directory, audits every local declaration for
unsafe code, local axioms and unapproved axioms, then replays nine main modules
with leanchecker. Twelve intentionally false clients must fail for mathematical
reasons. Import errors and missing objects do not count as rejection evidence.
The permitted axioms are propext, Classical.choice and Quot.sound.

Trust and limits
Only public dependency caches from .lake/packages are reused. The dependency
project's own build cache is excluded. This is not an independent rebuild or
authentication of every dependency binary, the compiler or the machine. Hashes
detect changes relative to this package; they are not a signature or a proof of
authenticity. Inspect source statements and premises as well as the success flag.
Compilation establishes the formal statements under their premises. It does not
establish that a physical robot satisfies those premises.

assemble.py is a workspace-side packaging script, not part of portable replay.
It is retained for provenance. It needs the original workspace layout.
The package and its new wrapper still require independent packaging review.
Licensing and public release remain pending owner review. No paper is submitted.
