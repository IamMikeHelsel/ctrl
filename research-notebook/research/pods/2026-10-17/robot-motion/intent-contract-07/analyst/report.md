# A task contract for hold and intentional movement

Status: candidate, not a new proved theorem or executed comparison. Recommendation: GO for one small position-contract proof; do not claim a full endpoint guarantee. No new plant runs, tuning, proof edits, or intent classifier were made.

Numeric targets alone do not identify intent. An observation of 1 mm can mean noise around a true 0 mm hold or a true 1 mm move. With a 0.2 mm task tolerance, the two required position sets are disjoint. A controller given the same observable history cannot guarantee both. It needs additional task information or an assumption that excludes one case.

The smallest practical addition here is an authoritative distinction between **keep the current goal** and **revise the goal**. A revision also needs a target or acceptable set, a deadline, and a bounded delivery/commit delay. This is not a claim about a minimum bit count. Correct task authority is an external assumption. Separating intent from estimates is established engineering and is not specific to FIR.

## Concrete contract and theorem candidate

Use two message roles: `OBSERVE(y)` is advisory; `REVISE(epoch, g, D, H)` changes the authoritative goal to g, requires position arrival by D, and keeps that request in force through H >= D. An initial goal a is authoritative. Advisory sequences do not advance, cancel, or replace the authoritative epoch. Duplicate/conflicting revisions need a deterministic upstream policy. A rejected revision is a failed task request, not a successful hold.

The bounded theorem covers an isolated revision from a completed reference tail. Let s be its issue time, c its causal admission time, and tau its execution time. All prior reference events have completed by s, their final reference equals the authoritative a, and no future motion is pending. Keep those events unchanged. Append `(tau, g-a)`, with tau >= c >= s. The revision remains authoritative through H. This excludes mid-move replacement; an extension must explicitly authorize the old committed path while a new request waits.

Require delivery plus admission within L+B+T_tick of s, and execution delay tau-c <= Q_max. Here L bounds communication, B bounds processing, and T_tick bounds waiting for an admission tick. The sufficient timing contract is

    D - s >= L + B + T_tick + Q_max + 4h.

The executable decision should check the actual `D >= tau + 4h`. Unbounded delivery, indefinite queueing, repeated supersession, or an unavailable clock bound cannot support a fixed response deadline. The old hold obligation ends when the true move is issued; the allowed transition region must contain the old and new goal. A new tight hold set cannot be required immediately when it is disjoint from the current one.

Retain all certificate03 assumptions: positive h, sigma and R; the stated classical plant/controller trajectory equations; actuator rate in [8 sigma,12 sigma]; disturbance magnitude at most W; initial transformed tracking cube; and `W + J/(48 sigma) <= 2 sigma^2 R`. Require the old history's exact guard and `2|g-a|/h^3 <= J`. The new event starts after the old tail, so their jerk supports do not overlap. The accepted exact history guard remains authoritative. No tracking state or physical state is reset at c or tau.

Write delta = g-a and use the already verified primitive

    F(z) = (1/24) sum(i=0..4) (-1)^i choose(4,i) max(z-i,0)^4.

For tau <= t <= H, the retained history gives `q(t)=a+delta F((t-tau)/h)`. The next proof must establish from this primitive that `0 <= F <= 1`, F is nondecreasing and `F(2)=1/2`, and import the verified tail fact `F(z)=1` for z >= 4. The derivative on [0,1] is z^3/6. On z=1+u, 0<=u<=1, it is `(1+3u+3u^2(1-u))/6 >= 0`; the remaining two intervals follow by the derivative's symmetry. The piecewise-linear third derivative has knot values 0,1,-2,1,0, which gives the isolated event's jerk bound. The new inequalities are proposed proof work, not assumed regularity or a new Lean result.

Compose these facts with certificate03's tracking result `|x-q| <= R`. For delta != 0 and tau <= t <= H:

    min(a,g)-R <= x(t) <= max(a,g)+R
    |x(t)-g| <= |delta| (1-F((t-tau)/h)) + R
    sign(delta) (x(t)-a) >= |delta| F((t-tau)/h) - R.

Before the move, the completed-tail hold gives `|x-a| <= R`. At tau+2h, directed progress is at least `|delta|/2-R`. At tau+4h and through H, `|x-g| <= R`. The zero-delta case is a hold. A positive progress guarantee requires `|delta| F > R`; this tube alone cannot certify progress of arbitrarily small moves.

For the existing 20 mm move, h=0.2 s, R=0.2 mm, issue=0.20 s, availability/admission/execution=0.22 s: the candidate gives at least 9.8 mm directed physical progress at absolute time 0.62 s and position arrival by 1.02 s. The deadline is 1.5 s. Peak reference jerk is 5 m/s^3, below 7.5 m/s^3. These are analytic conditional bounds, not new measured results or an optimal settling-time claim.

**Endpoint gap:** after reference rest, the generic tracking bounds only give `|v| <= 8 sigma R = 0.016 m/s` and `|a| <= 64 sigma^2 R = 1.28 m/s^2`. They do not imply the benchmark limits 0.001 m/s and 0.02 m/s^2. The candidate proves position hold/arrival/progress, not physical rest, full endpoint success, or a full-arm task. Arbitrary bounded disturbance is not a decay assumption.

## What the other contracts can and cannot supply

| Design | Information and guarantee | Limit relevant here |
|---|---|---|
| Deadband with a declared noise bound | If y=g+eta, `|eta|<=b`, and the held anchor a is exact, a strict b threshold prevents false revisions during a hold. A jump `|g-a|>2b` is detected at the first delivered sample. | This replaces an intent label with an amplitude-separation assumption. Smaller intentional moves can remain hidden forever. If the noisy sample becomes the goal, target error includes b. A threshold chosen to separate these known 1 mm perturbations from the 20 mm step does not validate general intent detection. |
| Set-valued command | An acceptable physical region G permits a reference in `G eroded by [-R,R]`. For a hold `[a-epsilon,a+epsilon]`, the reference margin is epsilon-R. | An uncertainty set of possible true goals is different: all goals must be covered. For C=[l,u], the robust reference set is `[u-(epsilon-R), l+(epsilon-R)]`. It is empty if `u-l>2(epsilon-R)`. A confidence score requires a coverage model; it is not a deterministic truth guarantee. |
| Hysteresis or persistence | Separate enter/exit thresholds or a dwell rule can suppress switching when their signal assumptions hold. | They add delay and can suppress a real small move. They cannot distinguish identical histories with different task meanings. A dwell rule must fit the move deadline. |
| Authoritative goal epoch plus constraint governor | A stable request identifies the task. A governor can admit or delay motion to satisfy plant/reference constraints. | Feasibility, delivery and queue bounds remain explicit. A feasible hold fallback is not proof that a requested deadline was met. |

Here epsilon=R=0.2 mm. The sufficient eroded hold set is the single reference value a. This particular bound has no margin for deliberate reference motion inside the hold band. This does not exclude a tighter certified tracking radius; any such claim must bind its theorem and reference assumptions separately. No width, gain, tolerance, or R was changed in this investigation.

## Closest methods read

| Primary reading and exact scope | Established mechanism | Relation to this candidate |
|---|---|---|
| [Miskowicz, 2006, Send-On-Delta](https://www.mdpi.com/sensors/papers/s6010049.pdf), sections 2.3, 3 and 5; printed pp.53–56,60–61 | Report a value when its difference from the last reported value crosses a resolution threshold. The paper studies reporting traffic and discusses sampled/background checking. | Supports a deadband reporting design. It does not establish that a threshold crossing means a robot task change, or give this physical hold/arrival guarantee. |
| [Hespanha, Liberzon and Morse, 2003](https://www.eng.yale.edu/controls/2003/hysteresis.automatica.pdf), section 2 with Lemma 1, section 3, opening of section 4; printed pp.264–267 | A hysteresis supervisor selects controllers from monitoring signals. Switching bounds require stated positivity and regularity/monotonicity conditions. The method addresses uncertain-system regulation. | Strong precedent for supervised switching. Its monitoring assumptions are not evidence that a packet identifies intent. This candidate does not invent hysteresis or supervisory control. |
| [Garone, Di Cairano and Kolmanovsky, author survey, 2017](https://merl.com/publications/docs/TR2016-102.pdf), sections 2.1–2.2 and 4.2; PDF pp.5–10,19–20 | Move the reference toward a request subject to an admissible-set condition, retaining a feasible previous reference as fallback. Bounded uncertainty is handled with constraint tightening. Constant-request convergence needs assumptions. | This is a close precedent for separating the requested goal from an admissible reference. Our proposed difference is a small checked composition with the retained FIR history and tracking theorem. No arbitrary deadline follows from convergence alone. |

The governor source is the authors' full-method survey, not a new attribution of the underlying results to 2017. The attempted original Gilbert/Kolmanovsky/Tan 1995 author-hosted PDF timed out; no full-text claim is based on it. This is a bounded reading, not an absence-of-prior-art search.

## Failure witnesses and next gate

- Identical 1 mm packets can require either a 0 mm hold or a 1 mm move. With 0.2 mm tolerance, no packet-only rule guarantees both.
- A real 0.5 mm move can remain below a 1 mm deadband forever. A wrong advisory label on the real 20 mm step makes an always-hold policy fail the task. Labels are a trusted input, not a solved inference problem.
- Zero reference derivatives now do not exclude an already queued future event. An immediate hold cannot erase that commitment. Require the complete old tail, or prove compatibility of every retained future event.
- For the 20 mm event, a deadline tau+0.4 s is impossible under this trajectory: its reference is then 10 mm and its physical position is within 0.2 mm of that value.
- An unknown true-goal interval [-1,1] mm cannot support a universal 0.2 mm goal guarantee. Choosing a convenient member silently changes uncertainty into permission.

The next worthwhile proof gate is the four-box monotonicity/range/midpoint lemma, an isolated retained-history reduction, and the three position inequalities above, with exact deadline and prior-tail premises. Add a concrete negative instance for an infeasible deadline and a pending old event. Keep all existing source files frozen. Do not extend to scheduling verification, small-move detection, or physical stopping in that gate.

The potential contribution is a precise, checked task-contract composition and a candid engineering case study. The control concepts and semantic separation are established. There is no demonstrated new control method or publication novelty from this investigation. Mike Helsel supplied the task framing and the concern that repeated target articulation can create unnecessary motion.

## Predeclared comparison, not executed

Keep accepted06 unchanged: 144 parameter cases, two resolutions, 288 traces; 144 endpoint and 66 full-task passes at each resolution. Its biased, irregular and random failures remain failures. Add a separately named, task-informed arm using the same six streams, four methods, three rates, two disturbances, controller, state continuity, clocks, tolerances, deadlines and horizons. This is 144 new parameter cases if later authorized, not a relabeling of old results.

All four methods receive the same authoritative sideband. The five true-zero streams keep authoritative goal zero; their original numeric packets remain unchanged advisory observations. The existing persistent_goal packet supplies one authorized 20 mm revision, issued at 0.20 s and delivered at 0.22 s. Do not reveal it earlier. This sideband comes from the known task truth and adds oracle-quality task information. It is not inferred from the packet values. Every baseline may solve the holds under this interface.

Preserve all original full-task checks and errors x-q, q-g_true and x-g_true. Report full-horizon hold, fixed-deadline position/speed/acceleration, settling through the fixed horizon, effort, command variation including its jump/continuous split, delivery/commit delay and every rejection. Count an infeasible or rejected intentional move as failure. Add the declared progress/arrival diagnostics at 0.62 s and 1.02 s for the real step. An always-hold policy must fail that step; there is no reward for waiting through it. Do not claim FIR superiority from gains caused by the shared task information.

The existing streams do not test label accuracy, small intended moves or mid-move replacement. No new streams or thresholds were added. `comparison-plan.json` records the exact overlay and unchanged case bindings before any possible execution.

User-requested industrial comparison axes are in `industrial-comparison-addendum.md`: native FANUC/Yaskawa interpolation, continuity across replacement, derivative order, and true energy versus effort proxies. These remain documentary comparators; the current scalar gate does not gain industrial methods or energy measurements. `motor-control-addendum.md` separates the human evidence from robotic design hypotheses.
