# R11 domain review: coordinated moving-base optical execution

AI-authored; inherited root model, exact identifier unavailable. Original addendum and approved proofs are unchanged. This is an isolated declared scalar model, not a robot implementation or a claim about bird/IMAX mechanisms.

## Source and assumptions recovered

The frozen addendum at `/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/robot-motion/stabilization-research-addendum-2026-10-18.md` is explicitly preparatory research: no prior stabilization simulation/proof was supplied. It calls for a single actuator command owner, common units/frames and timestamps, retained physical/reference state, versioned goals/calibration and explicit timing/authority bounds. It distinguishes actual base disturbance rejection from smoothing goals, and treats small-gain composition as conditional on the real interconnection. The original scalar FIR tracking result is not already a moving-base optical theorem.

The institutional [Řezáč dissertation](https://wiki.control.fel.cvut.cz/mediawiki/images/e/e7/Diz_2013_rezac_martin.pdf) was downloaded to `domain_rezac.pdf` after the web reader rejected its size. The root owns chapter-level inspection; this role does not claim independently reviewing those chapters. The original source addendum had inspected only its abstract/title page. No biological mechanism or exact commercial rig is inferred.

## Prospective scalar contract

Before testing, the domain role declared:

- Base angle β, actuator angle q relative to that base, world optical angle θ=β+q, and admitted world reference r, all in radians with one sign convention and a common unwrapped local angle chart.
- Relative position actuator `qdot=40*(c−q)+w`, where c is a relative-angle command and additive physical rate disturbance |w|≤0.01rad/s. The rate40/s is assumed exact initially; no torque, inertia, backlash, resonance, angle wrapping or hardware identification is supplied.
- Coordinated ideal command `c*=r−β+(rdot−βdot)/40`. All quantities in a packet refer to the same time and frame/calibration version. The actuator-facing command is held from an accepted packet, not independently summed by competing writers.
- Reference/base rate bounds |rdot|≤0.1rad/s and |βdot|≤1rad/s, and Lipschitz rate bounds with constants1 and10rad/s². Acceleration may change at joins, but the rates themselves must remain continuous/Lipschitz. Total information age ≤3ms, e.g.1ms sample interval plus2ms transport delay with no losses extending that bound.
- Initial error |θ−r|≤5mrad. A prospective actual relative-speed limit1.5rad/s is checked below. Position travel and command-angle bounds require additional bounded r,β and are not globally established for an unbounded ramp.

Define e=θ−r, δc=c−c*(t). Algebra gives `edot=−40e+40δc+w`. The command Lipschitz bound is

    Lc = (0.1+1)+(1+10)/40 = 11/8 rad/s,
    |δc| ≤ 3/1000 * Lc = 33/8000 rad.

The standard variation-of-constants/comparison argument gives the conditional all-time tube

    |e(t)| ≤ exp(−40t)|e(0)| + (1−exp(−40t))*7/1600,

so the initial5mrad tube is invariant; the forcing floor is4.375mrad. This is a hand-derived continuous ODE bound supported by kernel algebra, envelope and face lemmas, not a fully formalized ODE execution theorem. Held commands make the equation valid on hold interiors/almost everywhere, with continuous state and the usual integral execution interpretation. No sampled trace is used to infer the tube.

The control contribution |40(c−q)| is bounded by1.465rad/s, but physical |qdot| includes w and is bounded by1.475rad/s<1.5. This distinction matters if the interface clamps control rather than physical speed. No saturation is invoked under these hypotheses; an active clamp changes the error equation and needs its own proof.

## Matched sensor extension and outer-loop boundary

A separately declared extension allows same-timestamp base estimate errors |βhat−β|≤0.0001rad and |βhatdot−βdot|≤0.005rad/s. Their extra command error is at most0.000225rad, giving a forcing floor0.0046rad and actual relative-speed budget1.484rad/s<1.5. This is not a certificate for arbitrary sensor errors or stale/reordered frame versions. The permitted timing and sensor errors consume most of the5mrad budget.

The inner guarantee follows the admitted r. It does not prove that r equals the intended visual target. `output_target_bound` explicitly requires the separate outer error |r−target|≤G before concluding |θ−target|≤E+G. A held outer velocity with discontinuous jumps violates the Lipschitz-rate premise used above; it cannot simply be plugged into this tube. A continuous rate ramp with bounded slope is a possible bridge, which the root studies separately.

The exact rate40 matters. With actual rate a and inverse feedforward still using40, an additional term `(1−a/40)*(βdot−rdot)` appears. A10% rate error can exceed the spare tube budget under the declared rates. Neither the delay tube nor correct frame algebra establishes robustness to that model mismatch.

## Exact delayed sampled experiment

`domain_sampled.py/json` fixes a=40, sample h=1ms, transport d=2ms, constant base rate v=1rad/s, r=0 and w=0. The experiment starts at the first release t=d with the same physical q=−vd, world error0, for every policy. The earlier sample at time0 supplies known β=0 and rate1. No physical state is reset during switching or the80 subsequent hold intervals; this is a finite experiment through t=0.082s.

The packet sampled at nh and released at nh+d commands

    c_n=−v*n*h+(m−1)*v/a,

where m=0 is coordinated, m=1 omits rate feedforward, and m=2 reverses its sign. With E=exp(−ah), the exact release-to-release recurrence is

    e_(n+1)=E*e_n+v*((d+(m−1)/a)*(1−E)+h).

Its equilibrium is `v*(d+h/(1−E)+(m−1)/a)`, and e_N is that value times1−E^N for the common initial error0. An alternating exponential series encloses E with exact Fractions; interval arithmetic and outward rounding give the serialized rational endpoints. At N=80:

| Policy | World error, radians |5mrad criterion at this time|
|---|---:|---|
| Coordinated |0.002401291864…|pass|
| Omitted rate feedforward |0.026382236765…|fail|
| Wrong rate sign |0.050363181665…|fail|

The recurrence derivation is hand mathematics; rational evaluation is exact. These are finite-time comparisons, not hardware or a full multirate visual-feedback proof. The plant is first order, so command jumps can jump qdot; no acceleration/jerk promise is made. The initial attempt to serialize large Fraction denominators exceeded Python's string-digit limit; the calculation was retained and the output now uses exact outward rational rounding rather than huge strings.

## Kernel evidence and recommendation

`domain_scalar.lean` proves coordinated residual algebra, omitted-rate bias, command age bound, convex exponential-envelope step and numerical age/control/physical-rate budgets (seven declarations). The first draft had an incorrectly targeted absolute-value rewrite and failed; its log is retained. `domain_sensors.lean` provides sensor error transport, inward tube-face inequalities, the measured budget and separate reference/target error composition. Producer success and independent replay are recorded in the role manifest; those components do not constitute a complete global ODE library.

The critic's six blackout/frame/nominal-rate lemmas were independently compiled by this role in `domain_critic_blackout.log`, all with allowed axioms. In particular, indistinguishable base evolutions impose an information-age floor even with ideal actuation, and nominal inverse cancellation is explicitly conditional on the actual actuator rate.

GO for a bounded retained-state scalar executor experiment with exactly one command owner and a separately admitted slow reference. HOLD on a complete optical-target guarantee until outer-loop rate bounds, target motion/observation error, clock/frame contracts and actuator identification are supplied. Correct frame subtraction alone is insufficient; the derivative feedforward, timing and physical response premises materially change the result.

Next discriminating test: compose the root's continuous outer-rate ramp with this inner model, retaining q and all packet/reference history. Verify its derived Vr/Ar bounds, then inject a packet carrying an old frame version, a missed age deadline and a bounded actuator-rate mismatch separately. Report rejection or a recomputed tube instead of silently reusing the nominal5mrad result.

Quality18/20 (faithfulness4,reproducibility4,discriminatoryvalue4,critique3,actionability3),90%. Subjective confidence high for the declared scalar algebra/exact recurrence; physical applicability and full outer-loop composition remain unassessed.

Important delay placement: the3ms age affects the held feedforward/reference command c. The model's internal q feedback is ideal and current. This result does not cover delayed inner-state feedback, the source's H1 extra filter inside a feedback loop, or arbitrary loop delays. No stability inference across those architectures is justified.

Final local status: all11 domain declarations compile exit0 with standard allowed axioms; the exact recurrence script passes scoped Ruff and was rerun after formatting. Independent critic replay is separately owned by that role. No entire repository or physical-execution test was run for these isolated role artifacts.
