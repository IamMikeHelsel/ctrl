# Private research addendum: stable outputs on moving robots

**18 October 2026 — preparatory research, not part of the accepted manuscript claims.**

Research direction and motivating analogies: Mike Helsel. Prepared with AI assistance. No implementation, new proof, simulation, hardware experiment, submission, commit, or push was performed for this addendum.

## Connection to the existing draft

This is a separate extension proposal for Mike Helsel’s *Treating the Tremors We Built into Robots: What a checked execution layer can promise*, dated 18 October 2026. The inspected manuscript is in `checked-motion-paper-v2/main.tex` and `main.pdf`, beside this addendum. Its latest file-changing commit is `b344b6a34d21df7f6485d80fd74e56e9eb09e507` in the local `ctrl-research-notebook` checkout. [L1]

The existing work checks retained FIR reference histories, exact jerk and acceleration bounds, a sufficient speed bound, finite execution-time selection, and a future commit bound to the exact live history and task. It also gives a conditional scalar physical tracking and terminal-band theorem. It assumes an ideal common clock and atomic live-state checking/update; the proof client accepts timing as input. It is not yet a live executor.

The physical result guarantees position within 0.2 mm of the return goal from 1.42 s, then speed within 1 mm/s and acceleration within 0.02 m/s² from 3.42 s, under its specified trajectory, initial-state, response and disturbance premises. It does not prove exact rest, a coupled robot result, or the numerical experiment’s faster 1.70 s terminal task.

Retained FIR has about 0.40 times the matched native planner’s squared-jerk integral, but about 2.09 times its extra forward travel. Native fast alone meets the tight deadline. A stronger offline smooth comparator improves FIR’s integral and travel while raising peak jerk. Thus neither a smooth reference nor lower integrated jerk establishes superior task performance or physical safety. [L1]

## Mike’s new inspiration and what the sources support

**Design question:** can a small execution layer preserve an intended world-frame output while the supporting body moves and high-level plans change?

Bird head leveling motivates separating the desired output from supporting-body movement. Gioanni’s pigeon study investigates eye and head stabilization during rotation, in darkness and with visual surroundings. Its abstract reports additive eye/head responses and frequency-dependent behavior. This supports investigating coordinated feedback and explicit operating ranges; it does not provide a ready-made robot controller or establish the mechanism of every observed bird head-leveling behavior. Only the abstract was inspected for this addendum. [S1]

Martin Řezáč’s 2013 dissertation studies airborne optical-axis stabilization combined with visual tracking. Its abstract explicitly addresses vision-induced delay, multirate control, dual-stage actuation, feedforward disturbance rejection, and input shaping, with laboratory and helicopter testing. These are directly relevant engineering leads. The title page and abstract were inspected; individual experimental claims and controller derivations require chapter-level review before reuse. [S2]

**IMAX-specific mechanism remains unverified.** Mike’s helicopter-camera recollection is an inspiration, not evidence that a particular IMAX installation used a specified gimbal, sensor, controller, or biological principle. Identify the exact rig and manufacturer documentation before making that connection in a paper.

Ruckig is an established baseline for online motion generation with position, velocity, acceleration targets and velocity, acceleration and jerk constraints, including synchronization across multiple degrees of freedom. It is a trajectory-generation baseline, not by itself a guarantee about the physical robot following that trajectory. [S3]

## Three distinct hypotheses

| Hypothesis | Existing evidence | Proposed discriminating intervention |
|---|---|---|
| H1: added lag changes feedback dynamics | The existing timing diagnosis reports a 50 ms command-filter time constant inside a loop with a 12.5 ms actuator time constant. With unchanged gains, a lightly damped mode appears near 4.92 Hz, with 1.88 s amplitude-decay time; the direct model has three poles at −40/s. No stale measurement or shifted timestamp is present. These are polynomial/numerical results, not new Lean theorems. [L2] | Hold clocks and update schedules fixed; vary filter time constant and compare unchanged gains with explicitly retuned gains. Measure damping, transient travel, and task completion. |
| H2: clock uncertainty, variable delivery delay, or irregular sampling causes bad handoffs | Not established by that timing result. The current commit theorem assumes an ideal common clock. | Separately vary clock offset/skew, transport delay, sample interval jitter, and out-of-order delivery. Preserve identical plant, command sequence, and filter. Compare declared timing with actual execution. |
| H3: interacting loops issue incompatible corrections or retain inconsistent state | Not established in the draft. Multiple loops can cooperate; their existence does not establish competition. | Use separately characterized inner stabilization and outer tracking loops; vary relative rates/gains and arbitration. Compare each loop alone, coordinated composition, and deliberately inconsistent state/frame versions. |

These are hypotheses about specified systems, not a universal cause of robot tremor. Plant resonance, saturation, estimation noise, discontinuous goals, numerical artifacts, and mechanical effects remain alternative explanations. The first experiments should deliberately exclude or isolate them rather than silently fold them into “timing.”

## Proposed minimal library contract

Begin with a scalar, deterministic reference executor. Treat multidimensional and world-frame stabilization as later extensions.

**Inputs.** A versioned goal and task deadline; units and coordinate-frame identifiers; velocity/acceleration/jerk limits; retained reference history and current reference jet; request and measurement timestamps with clock-domain identity; uncertainty bounds and validity horizon; plant-state estimate with explicit error envelope where a physical claim is requested.

**Operations.** Propose an execution time from an immutable snapshot; validate the candidate against its future start state; atomically commit only if live history, task, frame/calibration versions and timing still match; evaluate the committed reference at a stated time; report rejection or expiry with an explicit reason. Retain a single owner of the actuator-facing command stream.

**Outputs.** Accepted/delayed/rejected status, actual scheduled start, checked reference bounds, final target/deadline obligation, certificate identity and assumptions, plus diagnostic timing records. The interface must distinguish planned reference state from measured physical state.

**Invariants sought.** Preserve committed history and the relevant reference derivatives through handoff. Reject stale or duplicate proposals. Never reinterpret an old-frame vector in a new frame. Never hide computation time by backdating execution. Do not reset the physical state when replanning.

**Fallback.** Retaining the existing plan is the draft’s rejection behavior. It may continue motion away from a new goal. A separately specified controlled-stop or emergency response belongs to the robot integration contract; it must not be labeled safe merely because it is smooth.

**Runtime boundary.** The first prototype can use ordinary runtime evaluation backed by offline checked mathematical components. It must not promise per-cycle Lean proof generation or hard real-time capacity before timing measurements. Memory and queue bounds require an arrival-rate or admission policy; pruning completed events alone does not bound active history.

## Staged experiments — proposed, not run

1. **Recover the fixed result.** Reproduce the saved H1 model from its exact coefficients and state, including the direct and filtered poles. Freeze inputs, tolerances and analysis before variants. A failure to reproduce stops interpretation.
2. **Isolate timing mechanisms.** Use the scalar plant with a deterministic event simulator. Sweep each H2 factor independently, then predeclare interactions. Include zero-jitter controls, fixed-latency controls, missed deadlines and out-of-order requests. Retain the old plan during computation.
3. **Study loop composition.** Add explicit base motion, a fast output-stabilization loop and slower goal/visual loop. Declare their frames, signals and authority. Compare coordinated and inconsistent handoffs. Separate actual base disturbance rejection from merely smoothing goal updates.
4. **Compare motion policies fairly.** Include direct commands, the existing retained FIR contract, native fast and duration-matched Ruckig, and a stronger smooth baseline where applicable. Start from the same moving reference and physical state. Count planning/verification/dispatch delay. Match task, bounds and initial conditions; record when different objective functions remain.
5. **Later integration gate.** Only after simulation and theorem review, select a real robot/interface, identify latency and tracking bounds, and design a separate hardware protocol with appropriate limits. Hardware work is outside this addendum.

For every stage record reference and actual position/velocity/acceleration, reference and actual peak jerk, integrated squared jerk, forward excursion, path length, task success, settling bands, acceptance rate, lateness, stale rejection and computation-time distribution. For stabilization add world-frame pointing error and disturbance-response gain/phase over a declared frequency range. Use command variation as a distinct metric; squared jerk is not motor energy.

Predeclare pass criteria from the task and model. Report all rejected requests, failures and sensitivity ranges. Sampled traces do not establish all-time bounds. Compare interactions only after the individual effects are identified.

## Candidate theorem work — obligations, not proved statements

**A. Robust future commit with bounded clock error.** Extend the existing ideal-clock commit rule. If commit and execution clock readings have error bounds εc and εe relative to one physical clock, a candidate sufficient ordering condition is
`estimated_commit + εc + dispatch_max ≤ estimated_execution − εe`.
This is only an ordering lemma under truthful bounds and a defined clock mapping. Clock drift over the validity horizon, sampling uncertainty, actuator scheduling semantics and atomic state binding must also be specified. It does not establish tracking or progress.

**B. Tracking under sampled and delayed execution.** Derive a concrete augmented error model including held commands, bounded delay, base disturbance and estimation error. Seek an invariant tube or input-to-state bound under a specified sampling interval, plant uncertainty class and feedback law. A possible proof route is a Lyapunov or Lyapunov–Krasovskii inequality, but the constants and feasibility must be derived. Do not assume that bounding jerk removes destabilizing phase lag.

**C. Coordinated loop composition.** After establishing subsystem gain bounds in explicitly chosen signal norms and domains, investigate a small-gain or passivity condition for the interconnection. A product-of-gains condition is only applicable after the actual feedback interconnection and delay operators are modeled. Saturation, switching, reference frames and internal integrator state require their own hypotheses.

**D. Conditional progress.** Acceptance soundness permits rejecting every request. A progress theorem additionally needs bounded computation/dispatch, a feasible task with margin, a candidate-generation coverage property, an admissible request rate or dwell time, and a scheduler policy. Prove a finite bound only under those conditions; do not infer completeness from a finite rejected candidate list.

**E. Physical output and frame transport.** A multi-axis/world-frame extension needs correct frame transforms and derivatives, coupled kinematics/dynamics, calibration/estimation error bounds and singularity handling. Componentwise reference limits do not establish Cartesian tracking, collision avoidance, contact safety or actuator effort limits.

The smallest useful next paper increment is A plus a measured runtime contract and falsifiable H1/H2 comparison. B–E are larger research tasks. Novelty must be judged against existing FIR planning, reference governors, verified execution, multirate control and online trajectory generation.

## Evidence and provenance

**[L1] Existing unpublished manuscript and portable proof package.** Local publication root:
`/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/robot-motion/`.
Manuscript: `checked-motion-paper-v2/main.tex`; proof boundary: `overnight-reviewer-bundle-v4/README.txt`. Existing claims summarized here were inspected, not rebuilt.

**[L2] Existing timing diagnosis.**
`/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/controls/timing-diagnosis-07/historical-sources.txt`.
Its stated polynomial/root evidence is recorded in that experiment’s `result.json`; this addendum does not independently recompute it.

**[S1]** H. Gioanni (1988), *Stabilizing gaze reflexes in the pigeon (Columba livia). II. Vestibulo-ocular (VOR) and vestibulo-collic (closed-loop VCR) reflexes*. DOI: [10.1007/BF00247311](https://doi.org/10.1007/BF00247311). [PubMed record](https://pubmed.ncbi.nlm.nih.gov/3259511/). PubMed returned an access challenge; abstract and bibliographic metadata were retrieved from Europe PMC using PMID 3259511.

**[S2]** Martin Řezáč (2013), *Inertial stabilization, estimation and visual servoing for aerial surveillance*, doctoral dissertation, Czech Technical University in Prague. [Institutional PDF](https://wiki.control.fel.cvut.cz/mediawiki/images/e/e7/Diz_2013_rezac_martin.pdf), title page and abstract (PDF pages 1 and 7).

**[S3]** Lars Berscheid and Torsten Kröger (2021), *Jerk-limited Real-time Trajectory Generation with Arbitrary Target States*. [arXiv:2105.04830v2](https://arxiv.org/abs/2105.04830v2). Abstract inspected; the existing draft already contains native Ruckig comparisons.

All external sources accessed 18 October 2026. No IMAX-specific source was verified. This document introduces research proposals only and does not change the manuscript’s accepted scope.

