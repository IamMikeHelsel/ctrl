# R03 source recovery (preparation, not timed research)

AI-written domain preparation. Runtime model inherited from root; exact identifier unavailable.

Frozen question: can a future trajectory commit remain bound to its exact history, task,
frame and timing snapshot under bounded clock error?

The source addendum is a proposal, not an implemented executor. Its referenced v4 bundle
contains `src/FutureCommit.lean`: `Base` stores exact event list, offset, width, version;
`Task` stores goal, request, absolute deadline, speed, acceleration, jerk limit, version.
`Pending` contains both full structures, execution timestamp, delta and finite candidates.
`baseOK` and `taskOK` check full structural equality, not merely counters. Accepted commits
append exactly `(execution, delta)` and increment version. Rejections preserve live history;
they do not satisfy the new task. No reference or physical state is reset.

`commitOK` explicitly assumes its predicates refer to one atomic read and ideal clock.
`timeOK` checks request <= completion <= commit and nonnegative dispatch with
commit + dispatch <= execution. The successful theorem binds the actual resulting reference
history and live task, including the full earlier reference jet and eventual reference rest.
It does not supply atomic machine instructions, measured timing, clock-domain translation,
frame/calibration fields, actuator scheduling, progress, or a general physical executor.

The addendum proposes units/frame IDs, calibration versions, immutable snapshots, validity
horizons and clock-domain identities as additional inputs. A sufficient ordering inequality
uses the latest possible commit plus dispatch against earliest possible execution. This is
not by itself a refinement of the original absolute-time trajectory: the meanings of all
stored event timestamps and deadlines must also be retained or revalidated consistently.

Planned domain contribution: explicit typed snapshot/atomic-install model; a clock gate
which includes the elapsed time from observation to linearization, drift validity, and
nonnegative dispatch. Independent tests will distinguish stale full snapshots, time-only
expiry while all data remain unchanged, and the version-counter-only shortcut. Runtime
linearizability and physical scheduling remain explicit assumptions.

Inspected original files (read only):
- `/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/robot-motion/stabilization-research-addendum-2026-10-18.md`
- `/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/robot-motion/overnight-reviewer-bundle-v4/README.txt`
- `/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/robot-motion/overnight-reviewer-bundle-v4/src/FutureCommit.lean`
- `/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/robot-motion/overnight-reviewer-bundle-v4/src/FutureCommitFixtures.lean`
