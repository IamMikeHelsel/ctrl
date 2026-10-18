TASK CONTRACT 08

TaskShape.lean proves the four-box primitive's monotonicity, [0,1] range,
midpoint and isolated jerk bound from the existing truncated-power formula.
IsolatedHistory.lean retains the complete old list, derives the isolated step
from its completed tail, and proves exact rational guard acceptance.
TaskContract.lean derives hold, transition bounds, directed progress and
position arrival from the actual plant trajectory and checked_tracking.
TaskFixtures.lean instantiates the fixed20mm request and proves failure of the
specific halfway deadline. It also preserves a guarded pending-event witness.

The final theorem is checked_isolated_task. It requires a correct authoritative
goal, all old event tails completed by issue, the old final goal equal to the
authoritative anchor, and causal execution. The exact guard for the appended
full list is a conclusion. Physical assumptions and the initial tracking cube
at time0 remain explicit. No tracking state or physical state is reset.

Physical rest and full endpoint success are open. These scalar proofs do not
certify Franka dynamics, torques, Cartesian mapping, contact or a hardware demo.
No numerical or native experiment was run in this proof gate.

To reproduce without changing frozen evidence, copy this directory to a new
sibling location, excluding .cache and __pycache__, then run python3 verify.py.
The verifier uses unchanged prior sources and pinned dependencies read-only.
It copies the full local source closure into an empty build directory, performs
a standard-axiom and unsafe-declaration audit, runs separate kernel replays,
and checks three false claims. Original sources and hashes are checked again.
The local build cache is disposable. The manifest preserves sources and logs.
Repository notebook sync and Git operations belong to the parent task.
