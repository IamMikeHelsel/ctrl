# Ten robotics/vision targets and the robot-smoothness program

Selected October 19, 2026. AI disclosure: OpenAI Codex program manager subagent.
Status: researched proposals, not ten achieved results. No hardware experiments are claimed.

## Decision and sequencing

Keep three lanes explicit: finish the seven-smooth proof and novelty audit, then prioritize the
robot-tremor experiments; keep the eleven-smooth extension secondary; develop this ten-target
vision portfolio and a practical clock-aware command/estimation layer for research robots.
The vision and middleware lanes share
experiments, but a useful engineering library does not automatically constitute new research.

Mike's timing hypothesis is testable: asynchronous acquisition, stale state, variable sample
intervals, and unsuitable control tuning may cause tremor. We have no evidence that these cause
**most** tremor. Friction, backlash, quantization, saturation, structural resonance, estimator
resets, and inner-loop bandwidth remain competing explanations. A nominal 1 kHz loop does not
imply that camera data or target commands are 1 kHz or synchronized.

Start with **V1, V2, and V3**, which can produce exact counterexamples and replayable simulations
without training a foundation model. V4 and V5 are the next mathematical extensions. The
remaining targets require more data or stronger novelty evidence before substantial compute.

“Baseline” below means the strongest directly relevant comparison identified in this scoped
review, not an exhaustive claim of global state of the art. All proposed gaps are hypotheses;
each must survive comparison with the cited work before being advertised as a research result.

## V1 — Acquisition-time intervals across vision and robot clocks

**Gap.** A calibrated constant camera/IMU offset does not itself bound the current acquisition
time when clocks drift, packets queue, or exposure varies. Arrival time and measurement time
can disagree even when the estimator looks smooth.

**Baseline.** Kalibr estimates spatial/temporal calibration; VersaVIS includes exposure
compensation and host-clock translation. Reimplementing these is not new. The candidate is an
online clock-uncertainty interval exported with each visual estimate and consumed by control.
[Kalibr](https://github.com/ethz-asl/kalibr), [VersaVIS](https://github.com/ethz-asl/versavis).

**Test.** Inject known offset, drift, timestamp quantization, bursts, and reordering into a
synthetic visual/proprioceptive trajectory. Compare constant-offset alignment, arrival-time
alignment, and interval alignment. Check interval containment and control error separately.
Use Kalibr example bags for a real replay after preserving their original timestamp semantics.

**New result / kill.** A useful result would certify containment under explicit clock-drift and
transport-delay assumptions and reduce false corrections versus existing synchronization at
matched buffering latency. Kill the novelty claim if it reduces to standard clock bounds or
its gain comes entirely from delaying every stream.

## V2 — Visual velocity estimates that do not turn timestamp jitter into torque noise

**Gap.** Differentiating positions with nominal frame spacing can amplify timing error; merely
using actual spacing can amplify measurement noise when successive timestamps are very close.
The desired interface supplies velocity and an uncertainty bound to the controller.

**Baseline.** Compare causal local polynomial fitting, a correctly discretized Kalman observer,
and the authors' 1€ filter. Adaptive smoothing already balances jitter and lag; it is not a new
idea. [1€ paper and reference implementations](https://gery.casiez.net/1euro/).

**Test.** Feed identical continuous trajectories, noise, and timestamp traces to all estimators,
then the same plant/controller. Include constant velocity, reversal, stop, and contact-like
velocity changes. Evaluate derivative error, phase lag, tracking error, torque spectrum, and
actual plant jerk using the simulator's true timestamps, not a nominal-step derivative.

**New result / kill.** Seek a sharper causal error-to-control bound with bounded acceleration,
timestamp error, and irregular sampling, or a clear Pareto improvement over the baselines.
Kill if the improvement disappears at matched lag/bandwidth or requires acausal samples.
Synthetic data first; DROID can test lower-rate visual motion but is not presumed to contain
the high-rate telemetry needed to diagnose a 1 kHz servo.

## V3 — Freshness-aware jerk-limited command reconstruction

**Gap.** Sparse visual targets are often held, queued, or extrapolated into a fast servo.
A smooth planned trajectory can still be evaluated at the wrong execution time, and stale
targets can trigger reversals. Require explicit behavior for missed deadlines and expired data.

**Baseline.** Ruckig already generates jerk-limited trajectories and exposes evaluation at a
specified time; its Pro tracking interface already predicts ahead. MoveIt Servo provides
Butterworth, acceleration-limited, and Ruckig smoothers. Compare those, not only raw zero-order
hold. [Ruckig paper](https://arxiv.org/abs/2105.04830),
[reference code](https://github.com/pantor/ruckig),
[MoveIt Servo](https://moveit.picknik.ai/main/doc/examples/realtime_servo/realtime_servo_tutorial.html).

**Test.** Hold the continuous target and plant fixed. Vary camera rate, command rate, jitter,
loss, and packet age; use actual actuator times. Compare correctly timed Ruckig, interpolation,
predictive hold, and the proposed expiration/fallback contract. Include saturation and reversal.

**New result / kill.** Seek a feasible-set theorem combining bounded age, braking authority,
and velocity/acceleration/jerk limits, with a library that reports when it cannot meet the
contract. Kill if it is just Ruckig with corrected timestamps, or smoother commands hide worse
tracking, overshoot, instability, or delay. That outcome may still justify an integration fix.

## V4 — Per-feature age and rolling-shutter collision margins

**Gap.** Treating a full image as simultaneous can produce different geometric error across
rows. Combine uncertain exposure/readout timing with bounded relative motion, rather than
inflating all obstacles by the same frame-age radius.

**Baseline.** Kalibr already supports rolling-shutter calibration, and self-calibrating VIO
already analyzes time-offset/readout observability. The candidate is the downstream control
clearance contract, not identification of rolling shutter.
[Kalibr](https://github.com/ethz-asl/kalibr),
[observability paper](https://arxiv.org/abs/2201.04989).

**Test/data.** Render a translating/rotating camera and a thin moving obstacle with exact row
timestamps. Compare global-frame, worst-case uniform, and per-ray swept envelopes. Vary skew
and readout error; measure missed collisions and the amount of usable free space.

**New result / kill.** A tighter certified envelope at the same assumptions and no more misses
would be meaningful. Kill if a standard reachable-set bound gives the same envelope or if the
required per-row clock metadata is unavailable. Unknown space must not become free space.

## V5 — Correlated pose/depth errors in controller-facing clearance

**Gap.** Camera pose and reconstructed depth can share errors. Independent inflation can be
overconservative; ignoring correlation can be unsafe. Preserve a joint uncertainty set through
the camera-to-robot transform and derive a usable support bound for a swept robot link.

**Baseline.** Splat-Nav supplies geometric collision constraints; SAFER-Splat supplies an online
map-based CBF. These establish that navigation with splat maps and safety constraints is prior
art. Compare full joint-set optimization and independent interval/ellipsoid inflation.
[Splat-Nav](https://arxiv.org/abs/2403.02751),
[SAFER-Splat](https://arxiv.org/abs/2409.09868).

**Test/data.** Begin with an exact two-dimensional pose-depth counterexample, then sampled
SE(3) uncertainties and known geometry. DROID stereo/calibration can supply realistic camera
configurations; it cannot by itself certify a worst-case error set.

**New result / kill.** Seek a cheaper certified bound that retains useful correlation and wins
against a strong robust-optimization baseline. Kill if improvements rely on an uncalibrated
covariance assumption or amount only to standard Lipschitz inflation.

## V6 — Sequence-level perception confidence after feedback changes the data

**Gap.** Framewise confidence is not an episode-level collision guarantee, especially when
errors cluster near repeated occlusions and actions change what is observed.

**Baseline.** Perceive with Confidence already provides statistical navigation assurances and
explicitly addresses planner-induced state shifts. Do not claim that joining conformal
perception to planning is new. Compare its assumptions with episode-block calibration and
simple union bounds. [PwC](https://arxiv.org/abs/2403.08185).

**Test/data.** Use simulated episodes with controlled persistent failure modes. Calibrate on
whole scenes/episodes, keep test scenes disjoint, and change the policy or active camera path.
Measure episode failure and set size, not only pooled pixel coverage. DROID can test sequence
statistics; simulated ground truth is needed for a collision-risk experiment.

**New result / kill.** A valid sequential guarantee under explicitly weaker dependence or
policy assumptions would count. Kill if PwC already covers the proposed setting or the result
merely restates marginal conformal coverage. Unrestricted distribution shift remains unsupported.

## V7 — Occlusion and reacquisition without velocity spikes

**Gap.** A tracker may return a plausible position after an occlusion while its implied velocity
jumps. Feed a set of possible target states during missing observations and require a
reacquisition transition compatible with command limits.

**Baseline.** CoTracker3 provides visibility/confidence; D4RT jointly models scene motion and
geometry. Compare their predictions plus constant-velocity/Kalman fallback and gated updates.
[CoTracker3](https://github.com/facebookresearch/co-tracker),
[D4RT](https://d4rt-paper.github.io/).

**Test/data.** Synthetic occlusion with known motion and distractors first; then public Kubric
sequences linked by CoTracker and selected DROID interactions. Separate correctly rejected
identity switches from needless freezing of a valid target.

**New result / kill.** Seek a quantitatively tighter bounded-motion reacquisition set and
constraint-preserving handoff. Kill if ordinary innovation gating plus jerk-limited replanning
matches it, or if it “succeeds” by refusing nearly all reacquisitions. Learned visibility is not
an unconditional guarantee of object identity.

## V8 — Map corrections that preserve local control continuity

**Gap.** Loop closure, scale correction, or extrinsic recalibration can abruptly change a visual
target/map. A physically unchanged scene must not generate a spurious derivative; a real
correction must still change collision margins when warranted.

**Baseline.** ROS REP-105 already separates continuous `odom` from discontinuous `map`.
Compare correct frame separation and atomic transform updates before inventing new smoothing.
[REP-105 source](https://raw.githubusercontent.com/ros-infrastructure/rep/master/rep-0105.rst).

**Test/data.** Inject known SE(3) and Sim(3) corrections into a synthetic trajectory and an
offline visual reconstruction. Test coordinate-only changes, genuine geometric corrections,
and stale transforms separately. Check command continuity, clearance, and reset energy.

**New result / kill.** Seek a hybrid reset condition preserving a safety/passivity budget under
bounded map correction and asynchronous transforms. Kill if standard frame handling solves the
entire issue. A coordinate-invariance identity alone is not a new control theorem.

## V9 — Metric/gauge correction with bounded temporal derivatives

**Gap.** Better per-frame geometric accuracy can coexist with worse velocity/acceleration when
scale anchors flicker or corrections change between frames. Evaluate the corrected trajectory
as a control input, not only a reconstructed point cloud.

**Baseline.** VGGT-Ω and DA3 are current geometry references. GAUGE already performs groupwise
radial correction with sparse metric anchors and studies imperfect anchors. Our candidate is
a causal correction whose derivative/error tradeoff is quantified. Use the September 18
VGGT-Ω reference checkpoint, not an older checkpoint without recording the distinction.
[VGGT-Ω](https://vggt-omega.github.io/), [DA3](https://depth-anything-3.github.io/),
[GAUGE full text](https://arxiv.org/html/2609.32596v1).

**Test/data.** First inject known scale drift and anchor loss into exact tracks; then use a
released tracker on synthetic or DROID clips with independently available metric references.
Compare GAUGE and causal regularization at equal anchor budget and lag.

**New result / kill.** Require reduced controller-relevant error without sacrificing geometric
accuracy beyond a declared bound. Kill if ordinary causal smoothing matches it or metric ground
truth leaks into the test correction. D4RT is a paper baseline unless an official usable release
is verified; an independent reproduction must be labeled as such.

## V10 — Schedule camera work before freshness becomes a control failure

**Gap.** A perception stack can spend GPU time on informative frames while a control-critical
estimate becomes stale. Schedule sensing/inference from a predicted margin-expiry time, with
resource limits and fallback behavior explicit.

**Baseline.** Splat-CBF already combines safety and information-seeking camera motion. Compare
it with fixed-rate inference, FIFO, and latest-only queues under identical compute budgets.
Do not claim active perception plus CBFs is new.
[Splat-CBF full text](https://arxiv.org/html/2609.23100v1).

**Test/data.** Simulate asynchronous camera/inference/control tasks with burst compute costs
and moving obstacles. Replay actual model runtimes only after establishing the scheduler's
assumptions. Rerun/MCAP can visualize capture, completion, and application times separately.

**New result / kill.** Seek a schedulability-and-safety condition that lets more useful work
complete at equal deadline violation risk. Kill if ordinary earliest-deadline-first/latest-only
scheduling performs equivalently or no bounded execution-time/age model is defensible.

## Practical library: what must be measured and delivered

Proposed interface: timestamped observations and targets carry source clock, acquisition-time
interval, receive time, sequence number, frame/version, and uncertainty. The adapter produces
commands evaluated at intended actuation time, limits/feasibility status, and a reason when it
must hold, replan, or request a stop. The exact fallback depends on the plant and authority;
“hold position” is not universally safe. Saturation and integral state need explicit handling.

The core should have a deterministic replay API and a small adapter boundary for ROS 2 or
libfranka. No allocations, blocking inference, file logging, or network waits belong in the
hard servo callback. Official FCI documentation specifies 1 kHz exchange and provides
`communication_test`; ROS 2 controller-manager diagnostics distinguish periodicity and
execution time. These are existing tools to reuse, not contributions to claim.
[FCI](https://frankarobotics.github.io/docs/overview.html),
[timing diagnostics](https://frankarobotics.github.io/docs/troubleshooting.html),
[ROS 2 controller manager](https://control.ros.org/jazzy/doc/ros2_control/controller_manager/doc/userdoc.html).

Passivity is a separate gate from smoothness. Prior work already relates impedance stability
to inner-loop bandwidth, filtering, and sample frequency, and handles delayed/rate-mismatched
teleoperation using passivity. Candidate theorems must account for actual sample intervals,
actuator saturation, and the sign convention for measured port power; bounded jerk alone does
not imply stability or passivity.
[Impedance analysis](https://arxiv.org/abs/1406.4047),
[delayed legged-manipulator teleoperation](https://arxiv.org/abs/2108.07658).

The first causal experiment is a factorial simulation: timing errors off/on crossed with
friction off/on, saturation off/on, and resonant dynamics off/on. Keep the target path, plant,
random traces, and task duration paired across methods. Include an oracle correctly timed
controller, a nominal-step controller, an actual-step controller, an explicitly tuned filter,
and correctly configured Ruckig. Plot a Pareto frontier over phase lag/tracking and smoothness;
do not select only the best smoothing parameter for our method. Report peak/RMS physical jerk,
tracking error, control effort spectrum, saturation duration, overshoot, passivity residual,
and deadlines. A smoother but slower robot is a tradeoff, not a causal discovery.

## Public data and compute gate

DROID exposes robot manipulation recordings, stereo views, calibrations, and actions; its
authors released improved calibration for many episodes. Rerun's example exposes joint states
and teleoperator commands and is suitable for inspection. Neither establishes that a selected
recording includes raw 1 kHz loop timing, torque, command-application timestamps, or high-frequency
tremor. Inspect the schema and sampling bandwidth before assigning a diagnostic role.
[DROID](https://droid-dataset.github.io/),
[Rerun example](https://rerun.io/examples/robotics/droid_dataset).

Use public recorded data and local/Spark synthetic probes first. No new credit purchases,
outreach, or physical-robot commands are part of this portfolio. The user's subsequently
authorized finite overnight self-check-ins are recorded in the PM report; they do not authorize
indefinite recurrence. Scaling
compute requires a surviving hypothesis, exact comparison protocol, and a saved result that
another checker can replay. Current status: selection and source review complete; these ten
experiments have not yet been executed in this document.

## Minimal reproducible simulation for V1–V3

This is an implementation specification, not an executed result. Build one deterministic replay
driver and three small probes. Save configuration, random seed, event trace, method parameters,
metrics, and failure reasons in JSON/CSV. Start with analytic identities and ten fixed seeds;
expand only after a failure mechanism and a competitive baseline are established.

### Shared clock and event model

Use SI units. Keep four separate times for every sample: true acquisition, device timestamp,
host receipt, and command application. The simulator knows true time; methods receive only
the fields their interface declares. Generate the entire event trace once per seed and reuse
it across methods. Never resample random noise inside a controller callback.

Nominal camera rate is 60 Hz and command application is 1 kHz. Test camera interval jitter
separately from servo interval jitter; do not change both in the first diagnostic. Clip generated
intervals to remain positive, and store the actual resulting distribution. Cases are:

| Case | Specific perturbation |
| --- | --- |
| Clean | Exact intervals, zero transport delay, exact clock, noiseless position. |
| Camera jitter | Camera intervals uniformly perturbed by ±20%; servo remains exactly 1 ms. |
| Servo jitter | Servo intervals uniformly perturbed by ±20%; camera remains regular. |
| Offset/drift | Device clock offset 5 ms and constant fractional rate error +100 ppm. |
| Queueing | Transport delay alternates between 2 and 20 ms in 0.25 s bursts. |
| Loss/reordering | Drop every twentieth frame; delay one preceding frame by 40 ms so it arrives late. |
| Timestamp damage | Duplicate one timestamp, reverse another, then introduce a 10 ms clock reset. |
| Correlated failure | Combine jitter, queueing, and losses using the same trace for all methods. |

These are chosen stress conditions, not measured distributions of real research robots. A
method must not use future samples or the simulator's true clock except in the labeled oracle.

### Probe V1: containment and identifiability, before control

Model host time as `t=a*c+b`, where `c` is device time. Initially allow `a` in the ±200 ppm
interval and `b` in ±50 ms. Each receipt `r` with declared transport delay in `[0,20 ms]`
imposes `r−20 ms ≤ a*c+b ≤ r`. Intersect these linear constraints and return the minimum and
maximum acquisition time for the next sample over the feasible set. A tiny 2D polygon clipping
implementation or independently checked LP is sufficient. Compare with a fixed-offset fit,
arrival-time timestamps, and the true-clock oracle.

Acceptance checks: all true acquisition times lie in the returned interval when assumptions
hold; interval widths and added buffering are reported; two offset/delay combinations that
produce identical receipts must remain indistinguishable. When a reset is signaled or the
feasible clock set becomes empty, report an inconsistent/invalid model. An out-of-envelope
delay or unannounced reset may remain observationally consistent with a different clock;
the receiver cannot promise to detect it. Include such an indistinguishable violation as a
negative control, and make containment conditional on the timing assumptions. Include a
constant-offset fit using a separate calibration segment so this is not
merely a comparison with uncalibrated clocks. Constant affine rate is an explicit limitation;
time-varying drift requires a different envelope before it can be claimed.

**Stop condition:** containment fails, interval information is no better than the declared
delay bound, or the proposed algorithm only reproduces a standard clock-feasibility method.
The last outcome is still usable middleware plumbing, with no novelty claim.

### Probe V2: an estimator test with exact expected outcomes

First use `q(t)=0.2*t` for one second with no position noise. Nominal-step differencing must
produce `v_hat=0.2*actual_interval/nominal_interval`; correctly aligned actual-step differencing
must produce exactly 0.2 up to floating-point error. This is a mandatory negative control,
not the research result. Arrival spacing is not acquisition spacing.

Then use `q(t)=0.1*sin(2*pi*0.5*t)` for ten seconds and a separate smooth reversal trajectory.
Add position noise with standard deviation 0.0005 rad, plus a bounded-noise version for any
deterministic theorem. Compare nominal difference, actual-time difference, a causal local
quadratic fit, a Kalman observer using each actual interval, and the reference 1€ implementation.
For close timestamps, a valid method may reject/merge data or expand its error bound; it must
not silently divide by zero. Filter derivative state consistently with the chosen implementation.

Measure velocity error against the analytic derivative, position error, and lag. For the sine,
estimate phase from sine/cosine coefficients at 0.5 Hz; also report amplitude attenuation.
Do not infer lag from a single global cross-correlation on a changing trajectory. Sweep the
baseline filter bandwidths, for example 2, 4, 8, and 16 Hz, using the same tuning split. Compare
the resulting error/lag frontier; allow interpolation between baseline settings for a fair
matched-lag comparison.

**Failure cases:** actual-time differentiation amplifies spatial noise on short intervals;
offset correction may be unobservable from stationary data; lag or smoothing may hide a target
reversal. Success on noiseless constant velocity alone only confirms implementation correctness.

### Probe V3: closed-loop replay and physical smoothness

Use a one-joint plant with state `(q,v,tau)`:

`q_dot=v`, `v_dot=(tau−2*v−f(v))/1`,
`tau_dot=(clip(tau_command,−20,20)−tau)/0.002`.

The inertia is 1 kg·m², damping 2 N·m·s/rad, actuator time constant 2 ms, and command limit
20 N·m. Baseline PD gains are `Kp=100`, `Kd=18`; use the same controller across command
reconstruction methods. The actuator model is essential: an ideal instantaneous torque jump
makes continuous physical jerk impulsive, so finite differences of commands would be a misleading
“physical jerk” metric. Here compute jerk directly from the state equations where differentiable.

The visual target is the V2 sinusoid, followed by a separate bounded-jerk reversal target.
Compare latest-sample hold, acquisition-time interpolation/extrapolation, a properly timestamped
Ruckig trajectory evaluated at actual command time, the proposed freshness-aware layer, and
an oracle continuous reference. Evaluate generated position, velocity, and acceleration together;
do not mix a smoothed position with an unsmoothed derivative. Keep Ruckig's planned constraints
distinct from guarantees on the actual plant state.

Integrate with an event-aligned RK4 step of at most 50 microseconds; split at receipt/application
events. Halve the step for a representative stress case and require reported metrics to change
by less than 1%. If they do not, fix numerical convergence before interpreting differences.

Run these negative controls separately before a full factorial expansion:

| Control | Purpose |
| --- | --- |
| Perfect timing, `f=0` | Any benefit attributed to timing should largely disappear. |
| Perfect timing, `f(v)=3*tanh(v/0.002)` | Friction can produce poor motion independently of timing. |
| Perfect timing, command limit reduced to 2 N·m | Expose saturation and tracking tradeoffs. |
| Add a flexible joint/load model | Check resonance as an independent explanation; publish its equations and parameters before comparison. |
| 100 ms visual blackout | Validate explicit freshness expiration and fallback, not unlimited extrapolation. |
| Duplicate/reordered packets and clock reset | Verify no stale command can overwrite newer state unnoticed. |
| Deliberately wrong inertia or delay envelope | Report simulation-ground-truth contract violations; detect runtime inconsistencies where observable, without claiming every hidden model error is detectable. |

Report RMS/peak physical jerk, tracking RMS/max, phase lag, torque RMS/spectrum, overshoot,
saturation time, deadline misses, and expiration count. If a passivity claim is made, additionally
define the physical input/output port, storage function, and sign convention; a positive tracking
performance score is not a passivity test. Do not insert an integrator without also specifying
its saturation/anti-windup behavior.

A provisional engineering advancement threshold is at least 20% lower RMS physical jerk with
tracking RMS no more than 5% worse and sine phase lag matched within 1 ms, without increased
limit violations. These are declared project thresholds, not statistical confidence levels.
Report paired per-seed differences and uncertainty, and report the full frontier even if the
threshold is missed. A new theorem would require explicit assumptions and a proof beyond
these simulations. Stop the timing-dominance claim if gains vanish after correct timestamp
handling or if friction/resonance controls explain the same effect better.

### First implementation boundary

The minimum deliverable is a replayable simulator and diagnostic report, followed by a small
timestamp/command adapter only if the probes justify it. No foundation-model training, robot
connection, hardware controller changes, or credit purchases are needed for these first tests.
