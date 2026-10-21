# S01 domain: one coherent infinite path from the actual C7/C8 constructors

AI-written domain research. Inherited root model; exact identifier unavailable. All new
files are isolated `domain_*` artifacts. Original constructors, frozen challenge statements,
source manifests, toolchains and active research files were preserved.

## Result and its boundary

The actual finite constructors support a source-bound infinite extension with the **same
ceiling**, for one fixed admissible braking input and one fixed set of globally bounded
rate, target-error and sensor-error streams. The key is prefix consistency, not compactness
of unrelated finite witnesses. Eighteen new lemmas compile against the original pinned
source closure with only propext, Classical.choice and Quot.sound. Independent critic
replays are recorded separately.

`global_execution` proves that a single diagonal C7 state is an actual source `Execution`
on every compact horizon, with both one-sided ODEs. `exists_coherent_global_handoff`
selects the original detector index once, then packages the corresponding finite C8
assemblies, generated detector readings, physical old-prefix preservation through arrival,
all sensor boxes and the unchanged ceiling for every nonnegative real time.

This is not existence for arbitrary time-varying future rate functions, arbitrary hybrid
controllers, Zeno schedules, physical robot dynamics, maintained rest or a stronger travel
margin. The admitted future class remains piecewise constant per digital cell, exactly as
in the finite source. The initial braking execution and its readings are supplied inputs.

## Source inspection and exact recurrence

Read both frozen reports and the original `ConstructiveClock`, `ConstructiveFlow`,
`ConstructiveHold`, `HandoffPrefix` and `HandoffAssembly` sources under
`/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-18/method-transfer-01/controls/`.
The authoritative C8 input copies and compiled `fresh-replay` closure were used for proofs.

Clock: h=1/2000 s, grid(n)=n/2000. The sampled-command latency is one cell. `state n`
is generated recursively from the SAME m,g,R,delta,epsilon, without a final-horizon
parameter. Its n-to-n+1 step pastes a newly generated exact held solution only after
`grid(n+1)`. Thus the existing `state_step_before` already preserves all times at or
before that boundary. Existing `measure_step`, `readings_step` and `command_step`
cover actual sampled readings and commands, not just the physical position.

`node_recurrence` depends on the previous two physical nodes: the command uses the prior
sample (the special initial reading m at index0, fresh state-plus-noise readings later),
while the new held solution starts from the next node. No terminal N occurs. In C8,
`hold ... N` is this constructor at N-1, and `trajectory ... N` joins it to the fixed old
braking history at grid(k). The first k old readings are retained; later readings are
regenerated from the new physical state. Changing N does not authorize a new m or noise
stream, nor preserve counterfactual future braking readings.

## Exact new proof chain

`domain_prefix.lean` (nine declarations):

- Arbitrary later stages n+k agree with stage n for every t<=grid(n+1).
- Actual readings and commands agree on the corresponding closed prefix.
- Sample, dispatch and index clock fields are definitionally independent of the state.
- Choose a finite covering stage for each t using the Archimedean property, and define
  `globalState` by evaluating that stage at t. Any two covering stages agree.
- The global state and its readings agree with every finite prefix on its covered domain.
- Invoke the actual source `finite_clearance` to preserve the original C7 ceiling at
  every t>=0, with no larger radius or extra dynamical premise.

The covering-stage choice merely selects an already stable formula. It chooses no new
control stream and is not an executable controller implementation. Causality is inherited
from the source's node recurrence and the prefix equalities.

`domain_global.lean` (two declarations):

- For any compact horizon H, use the finite stage covering H+1. This strict extra margin
  gives a neighborhood of every t<=H on which global and finite states agree. Transfer
  continuity and BOTH one-sided derivatives, including the final incoming derivative,
  with the actual readings and command. Then invoke the actual source `make_execution`.
- Apply source `actual_schedule` to the global state. Its contract already includes
  local finiteness of dispatches, so the resulting schedule is non-Zeno.

Point equality at an endpoint would not be enough for this step. The proof explicitly
uses an open interval below the larger finite horizon when transporting derivatives.

`domain_handoff.lean` (four declarations):

- Global hold equals source `hold N` for every covered local time.
- Global recovery-to-hold trajectory equals source `trajectory N` on its entire prefix.
- Generated `newReadings` agree through every covered reading index, including old-prefix
  readings and the initial handoff sample.
- Original C8 `assemble.safety` transfers to all real t>=0, with exactly
  `3013722449/20100000000`, equal to `3/20-1277551/20100000000`.

`domain_assembly.lean` (three declarations):

- Preserve the original physical state through `grid(k)+h`, not merely the detector time.
- Every generated reading for every natural index satisfies its actual `SensorBox`.
- Obtain k once from source `finite_first_guard ex hm`, before any horizon is chosen.
  Package `First m k`, all finite `Assembly ... k N`, first-index stability for generated
  global readings, the preserved physical prefix, all actual sensor boxes, and all-time
  same-ceiling safety. The final theorem does not add an assumed First index.

## Assumptions preserved exactly

The global future sequences R,delta,epsilon are fixed once. For every n>=1,
8<=R(n)<=12 and |delta(n)|<=1/100. For every n, sensor components obey
|epsilon(n,0)|<=1/1000, |epsilon(n,1)|<=1/100, |epsilon(n,2)|<=1/20.
The original pending `Execution` and Guard suffice for the C7 bridge. For C8 the original
`BrakingExecution` and `Readings` assumptions derive that pending prefix and guard via the
actual source detector. epsilon0 remains unused in initial sensing; the retained m is
still the first reading. Same grid, index, stamp, clipping rule, fields and noise boxes.

It would be invalid to choose unrelated finite R_N/delta_N/epsilon_N or independent
first indices per N and infer a single execution merely from arbitrarily long witnesses.
Here the source already accepts globally indexed streams; fixing them is the coherent
input interpretation, not a new future-execution premise.

## Verification and provenance

The original notebook toolchain was available: Lean4.35.0 at the research workspace's
`.tools/elan`, using its pinned `lean-controls` project. No fallback to ctrl4.33.1 was used.
`domain_compile.py` checks all27 copied-source SHA256 values against the original
`verification.json`, prepends only this card's directory to the recorded LEAN_PATH, and
writes local bridge oleans/logs. The27 source hashes bind the imported research modules;
the58-file historical build/kernel audit was not freshly repeated in this session.

Reproduce in dependency order with uv:

    uv run python .../cards/S01/domain_compile.py domain_prefix.lean
    uv run python .../cards/S01/domain_compile.py domain_global.lean
    uv run python .../cards/S01/domain_compile.py domain_handoff.lean
    uv run python .../cards/S01/domain_compile.py domain_assembly.lean

Each successful log prints the theorem axiom closure. Initial namespace and rewrite
failures are preserved in failed-attempt logs. A negative mutation replaces the covering
stage in `globalState` by stage0; it is saved separately and must fail rather than become
a promoted proof. That mutation tests the invalid idea that a finite constructor's
unrestricted outside-horizon formula automatically gives an infinite execution.

No numerical simulation or physical measurement substitutes for these source-bound
statements. No external novelty claim is made: the finite-prefix gluing mechanism is
standard; its value here is closing the actual model's previously explicit infinite
execution boundary with the same data and ceiling.

## Domain gate

GO for independent acceptance of this source-bound infinite extension, then a statement
review of whether the resulting every-compact-horizon execution is the desired public
infinite API. The current proofs preserve a conditional scalar model guarantee; they do
not validate plant calibration or improve precision/rest behavior. Further time is best
spent auditing prefix/reading/clock bindings and negative controls, not expanding the
class of allowed rate signals silently.

Quality estimate: faithfulness4, reproducibility4, discrimination4, critique4, actionability4
=20/20 (100%) for this narrowly scoped bridge, subject to independent final acceptance.
Subjective confidence high in successful kernel statements; no confidence claim about
physical applicability or novelty. PM owns final grade and decision.

## Final absolute-time execution bridge

`domain_absolute.lean` closes the explicit C8 local-to-absolute-time gap. Its five
lemmas compile with the original pinned Lean toolchain and only propext,
Classical.choice, Quot.sound:

- The single joined trajectory is continuous on every compact interval [0,H].
  A strictly larger finite horizon transfers continuity, avoiding an endpoint-only argument.
- Its absolute-time right ODE holds at grid(k)+s for every s>=0; its left ODE holds
  for every s>0. These use the same original rate, target, clipping, measurement and
  one-sided timestamp functions as Assembly.absolute_right/left. The source join
  derivative lemmas transfer the already checked global local Execution.
- `exists_infinite_execution` derives one k from the source first-guard theorem and
  binds every compact-horizon actual Execution, every actual non-Zeno schedule,
  joined-path continuity, the original pending prefix, and the unchanged safety ceiling.
  This complements the sensor-box/first-reading theorem in domain_assembly; it does
  not introduce an independent trajectory or independent guard index.

Run after the four previous modules:

    uv run python .../cards/S01/domain_compile.py domain_absolute.lean

Independent replay was requested only after the file was frozen. The original loss
and braking phase contracts remain phase-open: no derivative is claimed at t=1/20
merely from continuity. A separate `domain_phases.lean` makes their preservation explicit.

The final phase-preservation compile succeeded: `global_loss_ode` and
`global_brake_ode` have only the three permitted axioms. Reproduce with:

    uv run python .../cards/S01/domain_compile.py domain_phases.lean

Final producer result: 25 printed bridge declarations across six Lean files compiled
successfully. The compiler helper passes scoped ruff. Independent replay of the last
two modules is pending at this writing; this count is producer-verified, not a claim
that the full repository or historical research closure was rebuilt. No integrated CLI
or original research changes were made, so the repository-wide integrated-change
checks were not run by this worker.
