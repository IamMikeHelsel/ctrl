# C03 — Causal high-order reference feasibility

**GO for a typed admission gate that distinguishes necessary rejection, a sufficient reference certificate, and UNKNOWN.** AI-written four-role review. Root is PM; domain, inventor and independent critic inherit root model, exact identifier unavailable. No remote inference or plant/hardware command.

Original question: Can a compact admission rule reject impossible endpoint/deadline requests with bounded jerk, snap and latency before controller synthesis?

Source: `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/admission-04/analyst/report.txt`, SHA256 `5608830cdd54ed69455cce41cca47af38b4aa3647a6216721bb9c1112875046b`. The previous sharp zero-acceleration bound and rejected endpoint remain unchanged. The old request specified(q,v,a), not terminal jerk. The separate feasible0.6m stop task specifies(q,v,a,j) and5ms latency with old jerk held at+10.

## Prior work and crossover mechanisms

[Ruckig's primary paper](https://arxiv.org/abs/2105.04830) covers complete position/velocity/acceleration target states with jerk limits; the [official input API](https://docs.ruckig.com/classruckig_1_1InputParameter.html) exposes those limits and duration semantics. These are not automatically finite-snap or continuous-jerk guarantees. High-order planning, FIR motion shaping and reference governors are established prior art in the frozen report; this campaign claims no new planning algorithm.

1. **Reachability as a moment problem.** Endpoint derivatives are different integrals of the same jerk/snap history. Their separate feasible intervals form a relaxation; mixed support inequalities preserve their dependence. A certificate must bind initial state, terminal derivative requirements, time origin, hold policy and integration regularity.
2. **Unexpected transfer: bounded-density transport.** Under normalized snap bounds, adding a constant converts signed snap into a nonnegative measure with an upper density cap. PSD moment positivity alone permits a Dirac impulse and can falsely pass a request. The density cap carries the snap constraint and cannot be dropped.
3. **Resource accounting across latency.** Propagate the entire old reference state to execution time and spend the remaining absolute deadline. Zero acceleration is not rest; delayed execution cannot reset jerk, velocity or controller state.
4. **Polynomial convex-hull certificates.** A sufficient reference can use exact polynomial identities or Bernstein envelopes. Failure of that candidate is different from infeasibility of the endpoint request.

## Discriminating results

**Source-bound full-stop lower gate.** Adding terminal j(T)=0 to j(0)=J changes the lower envelope to max(J−St,−J,−S(T−t)). For the long-enough regime its integral is−JT+5J²/(2S), giving T≥a0/J+5J/(2S) for a(T)=0. At the source execution state a0=51/20,J10,S400, this is127/400=.3175s, exactly the duration of the saved three-phase blend. Arrival-to-blend end is129/400=.3225s. Velocity there remains positive, so it is not full rest. This terminal-jerk refinement is not silently imposed on the old three-component request.

A mixed moment gate using the actual retained execution state excludes a full stop at or before execution+7/8s, hence global1.13s. The optimized dual has a switching-regime condition; independent critique caught the missing bridge. A separate short-time velocity obstruction now covers that regime, and padding an earlier full rest preserves the constraints. The original1.5s deadline remains feasible by its unchanged piecewise reference. Dropping terminal jerk zero changes the necessary-test outcome, demonstrating that this contract field is load-bearing. Continuous ODE-to-moment integration remains a hand bridge; kernel results check the conditional algebra and inequalities.

**Componentwise feasible does not mean jointly feasible.** Inventor's normalized request(q,v,a,j)=(0,−1/16,1/8,0), from rest over T1 with J1,S1, has independent coordinate witnesses but violates a sharp mixed inequality. Its support polynomial and exact rational integrals are saved. A general necessary gate retaining arbitrary initial state is

`|A−2V/T−(3T/16)(jT−j0)| ≤ S T²/16`,

where A=aT−a0 and V=vT−v0−a0T. The normalized extremizer is not substituted for the original source trajectory. Critic supplies a separate exact envelope-based example and component witnesses.

**Sharp rest-to-rest snap diagnostic.** For a prospective rest-start/rest-end task, |snap|≤S gives displacement≤ST⁴/384. The extremizer uses snap signs+−+− at normalized switches(1−1/sqrt2)/2,1/2,(1+1/sqrt2)/2. Exact arithmetic in Q(sqrt2), independent replay, a cubic dual, and kernel pointwise/integral support helpers substantiate this bound; the full derivative-to-moment and piecewise integration assembly remains hand-derived. With T=.1,S400,J10, maximum displacement is1/9600m≈.104167mm, and the extremizer's jerk peak20(sqrt2−1)<10. A1mm request passes the separate position cap1/600m but fails the joint rest constraint. This is a new diagnostic task, not a replacement of the source0.6m task. Constant snap is a negative control for omitting the terminal moments.

**Bounded-density falsifier.** With terminal jerk zero, μ=(snap+1)dt is nonnegative with density≤2 and mass1. At zero terminal acceleration its mean is1/2. PSD moments alone allow zero variance and the spurious velocity−1/24; that would require a Dirac measure. The bounded-density minimum variance is1/48, attained by density2 on[1/4,3/4], giving velocity−1/32. These are exact rational/hand moment arguments, not an accepted SDP output.

**Constructive sufficient reference.** A separate prospective41.667micron move after5ms rest hold has100ms available. The septic shape35s⁴−84s⁵+70s⁶−20s⁷ has exact endpoint matching and all-time bounds V7/7680,A7/64,J35/16,S350, inside budgets1,3,10,400. Its nonnegative velocity preserves corridor[0,D]. Jerk is continuous and absolutely continuous; snap jumps at joins, so continuous snap or bounded crackle is outside this certificate. Kernel polynomial/range helpers plus independently differentiated coefficients support the hand time-scaling/trajectory bridge.

The isolated `pm_septic.py` prototype returns ADMIT_REFERENCE only for its declared family. The critic found negative latency admission and ignored extra constraints in an early version; those bytes/results are preserved. The repaired gate binds nonnegative latency, rest history, corridor, exact fields and AC-jerk/a.e.-snap regularity. All17 saved cases and9 independent probes pass. Unsupported states/regularity or insufficient polynomial bounds return UNKNOWN. No plant guarantee or production parser claim is made.

**Actual-source candidate failure.** A single full-state septic over the source's remaining249/200s reaches the exact requested endpoint and passes exact Bernstein position/velocity/acceleration/snap checks, yet jerk at quarter-duration is−951922405/73188736, outside±10. The kernel supplement checks this arithmetic; its coefficient/derivative/source binding is independently checked. The original piecewise feasible witness remains valid. Reject this candidate, not the task.

## Evidence and next action

Role reports and exact receipts: `domain.md`, `inventor.md`, `inventor_septic.md`, `critic.md`; accepted Lean hashes/counts/logs in `critic_acceptance.json`. Failed proof/parser and arithmetic drafts remain preserved and are not counted as accepted. No approved Challenge, prior controller or original reference was edited. Generic integral-support theorems are kernel checked; they do not automatically supply the source kinematic hypotheses, all-time physical execution or a universal feasible planner.

PM GO: after all60 initial reviews,30minutes on a manifest-bound admission consumer combining necessary dual rejections and independently checked sufficient piecewise-polynomial witnesses. Use the20 cases in `next_block_protocol.json`; preserve UNKNOWN when neither applies. Bind actual retained state, absolute deadline, units, corridor, terminal jerk and regularity. Require kernel rechecking of promoted certificate instances and expose every remaining integration bridge.

Quality rubric: faithfulness4/4, reproducibility4/4, discrimination4/4, critique4/4, actionability3/4 = **19/20 (95%)**. Subjective confidence is high in the scoped exact findings; general sufficiency, novelty and physical usefulness remain unquantified.
