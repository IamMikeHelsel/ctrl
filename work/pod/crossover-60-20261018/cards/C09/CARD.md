# C09 — Safe excitation for coupled-source identifiability

**PM gate: GO for a bound finite-window experiment/decision adapter. Physical sensing and actuation remain HOLD.** The useful result is a separating measurement with a derived leakage budget, followed by a joint uncertainty bound that permits correction without recovering drivetrain phase. This extends the question beyond S12's static action-set test. AI-written; root PM plus three reused domain/inventor/critic workers, inherited model with exact runtime identifier unavailable.

## Original question and evidence

Can a bounded intervention distinguish wheel imbalance from synchronous drivetrain forcing enough to change a safe control decision?

Frozen order22, controls wildcard. Read `coupled-measurements.txt` and `source-attribution/challenge.txt` under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/`, plus the fixed model. That prior experiment is real, signed-phase and static: wheel gain1 and separating leakage[.2,.3] are assumptions. Its trial does not identify baseline wheel imbalance. The original z=.625 and exact certificates are preserved; this review introduces a distinct complex experiment with z=.5.

The [official SAE2005 abstract](https://saemobilus.sae.org/papers/driveline-imbalance-sensitivity-testing-methodology-2005-01-2307) describes differential roll-speed order separation as prior art. Direct retrieval timed out; critic recovered the official abstract through search, not the full paper. [Köhler et al.](https://arxiv.org/abs/1911.02899v2) provide prior set-membership/robust-adaptation methodology. Neither source validates our toy sensor, phase actuator or support model. No novelty claim.

## Three crossovers and falsifiers

1. **Lock-in measurement and causal experiment design.** A wheel-synchronous finite-window complex measurement separates frequencies, but its leakage depends on the actual clock and frequency contract. Constant frequency offset uncertainty is not an arbitrary time-varying error model. Trial-mass sensitivity alone leaves two baseline sources confounded; duplicates do not add independent information.
2. **Joint set bounds and decision-focused estimation.** Reuse baseline and separating measurements together rather than fitting a wheel estimate and discarding shared nuisance constraints. The resulting correction can be safe for every retained nuisance phase. Falsifiers include wheel-phase miscalibration, source drift, missing quadrature and an empty/changed model. A phase rotation must be transported into the applied correction, not merely into measured numbers.
3. **Unexpected finite-window dynamics and phase cycling.** Two integrations by parts expose the exact endpoint-state correction needed to infer forcing from displacement. A retained free-decay state produces a false source if that term is dropped. Separately, ABBA phase cycling cancels affine nuisance drift, but slow phase authority makes quadratic drift expensive; bounded deterministic error does not shrink as independent-noise averaging would.

## Derived measurement and action result

For a declared complex/two-axis force signal, wheel-synchronous averaging gives z=w+L*d+e1. If the nominal frequency difference times the measurement duration equals2pi, actual difference has a constant relative error |delta|≤.01, and amplitudes/transfer remain fixed during the window, then |L|≤1/99. Unknown constant phase is included in L. The integral-to-sinc bridge is hand-derived; the sinc inequality has an isolated kernel proof. Averaged deterministic error remains bounded by its stated bound; no statistical gain is assumed.

Use b=w+d+e0, |e0|≤1/10, |e1|≤1/40, |w|,|d|≤2, and observed b=1,z=1/2. These are explicitly new complex data and constraints. Correction c=−z has wheel residual r=w−z. With K=|b−z|+.1=.6 and ell=1/99, retain the joint implications

`|r| ≤ eps + ell*|d|`, `|d| ≤ K+|r|`.

Thus |r|≤123/3920 and |d|≤495/784. Even after arbitrary nuisance phase rotation, every rho∈[0,1] gives mixed response at most1299/1960≈.662755, below the original illustrative.75 limit; wheel residual is below.125. This is tighter than the prior-only179/3960 wheel bound and the intermediate phase-free1367/1980 mixed bound. The bounds use all retained tuples, with no independence assumption.

An exact witness attains the final bound in the relaxed leakage disk, including baseline/separating errors and a final nuisance phase flip. It is not asserted attainable on the exact sinc curve. The sufficient detuning-error threshold for this abstract bound is2/29; eta=.08 has wheel bound71/840<.125 but mixed323/420>.75. Baseline-only worlds(w,d)=(0,1) and(1,0) admit no shared correction satisfying the wheel limit. A new nominal window with w=d=.5,L0,errors0 is a nonempty attainable positive.

## Negative controls that change acceptance

A real scalar sensor is not automatically the complex force channel: doubled demodulation also contains conjugate-frequency images. One explicit real-sensor case gives spurious imaginary response−4i/(3pi), far beyond the error budget. The two-axis force sensor is an explicit interface assumption. If displacement is measured instead, the exact identity is

`F_omega=(a+iomega)^2 X_omega + ([v exp(-iomega t)]+(2a+iomega)[x exp(-iomega t)])/T`.

Unknown a, retained endpoints and their errors must stay joint. Free decay with zero force refutes the steady-state-only inverse. A common pi phase-reference rotation preserves the numerical measurement gate but applying the correction without inverse phase transport can double wheel residual. A post-acquisition wheel-source change invalidates the old bound.

Clock binding has a decisive exact negative. With w=.5,d=.25, zero errors and a **half-beat** window, L=2i/pi and z=.5+i/(2pi). The real wheel residual after c=−z is1/(2pi)>.125. Incorrectly applying the one-beat bound predicts wheel<.03 and mixed<.47, falsely passing both gates. A256-pattern floating-point variable-frequency screen found no violation; that finite screen is not a proof extending the constant-offset theorem.

Changing relative speed also changes nuisance phase. The old phase-fixed.6 endpoint bound can fail; the new phase-free joint bound covers this without requiring exact phase closure. Nuisance magnitude and the wheel phase/transfer still must be controlled.

## Prospective dynamic intervention: explicit new toy

A normalized complex support satisfies x''+2a*x'+a²*x=f with **constant** a∈[1,2], retained |x0|≤1 and |v0+a*x0|≤1. Positive variation-of-constants kernels provide comparison bounds; full ODE/Python refinement is not kernel proved. Direct two-axis force sensing avoids claiming unit gain from displacement.

A separate speed-aware variant fixes base speed10, nominal relative-speed ramp0→.1 over10 time units, a one-beat holdT=20pi, and10-unit return. Actual constant phase-actuator gain is1+delta, |delta|≤.01. Drivetrain imbalance force scales by(1+nu/10)², so its gain is at most1.02030201. Probe force is bounded by4.04060402; the prospective travel limit4.1 is respected. The effective measurement leakage increases to11336689/1100000000. Joint inference still gives wheel residual171510067/5443316555 and post-correction force3609010067/5443316555≈.663017, for arbitrary nuisance phase.

The state is retained through return and correction. A declared active force-phasor actuator applies c(s)=−.5*(10s³−15s⁴+6s⁵) over one time unit, then holds−.5. Its amplitude≤.5 and slew≤15/16; no jerk limit is claimed. This is not mounting a mass on moving hardware. Convex interpolation keeps force within the probe envelope. After completion, the continued-force comparison is

`|x(s)|≤Fpost+(Fprobe−Fpost)*(1+s)*exp(-s)`.

An exact Taylor lower bound exp(6)>400 gives travel<.722125 after six further units, hence below1 thereafter. Probe duration<83 plus correction1 and comparison6 gives a conditional toy bound<90. The thresholds4.1/1 were chosen for this prospective diagnostic, not historical predeclared requirements. Persistent forcing permits a persistent oscillation: safety is not rest. True force removal has a separate decay certificate and cannot be inferred merely from ending detuning.

Physical phase/speed/force authority, torque/load effects, two-axis sensor calibration and the actual suspension remain HOLD. The toy specifies these interfaces instead of claiming they exist on the user's robot.

ABBA provides a separate unfavorable route: at phase-rate authority.1, sign-flip spacing near32 is needed. A bounded quadratic nuisance drift yields estimate1.012 for true wheel.5 even with zero measurement error, and naive correction−1 violates the wheel limit. This is a changed-drift diagnostic, not a refutation of the original invariant-amplitude model.

## Acceptance and continuation

Fourteen isolated Lean declarations independently compile with permitted axioms; exact producer/critic tests reconstruct joint bounds, phase/quadrature failures, oscillator comparison arithmetic and speed-aware budgets. `pm_lean_acceptance.json` and `critic_acceptance.json` record current hashes/logs. Integral/ODE composition, actual actuator realization and complete source-to-action software remain outside the kernel evidence.

GO after all60 initial reviews: one30-minute manifest-bound complex acquisition→joint update→retained-state action adapter. Freeze20 clock, phase, source-drift, gain, image, empty-set, state-reset, amplitude and termination mutations; test nontrivial accepted data and rejection cases independently. Promote the measurement integral and dynamic comparison bridges before claiming an end-to-end proof. Physical use remains HOLD pending measured interfaces. No hardware commands, publication or source changes occurred.

PM rubric: faithfulness4, reproducibility4, discrimination4, critique4, actionability3 = **19/20 (95%)**. Critic's separate rubric gives18/20. Subjective confidence is high in the stated exact arithmetic; physical usefulness and novelty remain unresolved. Actual substantive elapsed time is in state.json; ten minutes reviewed is not ten minutes proved.
