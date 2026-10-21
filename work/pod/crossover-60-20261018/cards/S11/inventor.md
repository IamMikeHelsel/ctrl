# S11 cross-discipline inventor

The useful path is a two-sided viability admission test followed by a maintained residual-motion contract. A first velocity zero supplies neither. No controller or clock in the accepted C8 construction was changed by this review. Model identity: inherited root model; exact identifier unavailable. AI-generated research notes.

## Source binding and prior result

Read the frozen S11 card and the C8 constructed-handoff, C1 milestone, and performance-level reports. Actual definitions were checked in C8 `inputs/DigitalHold.lean`, `inputs/WeightedEntry.lean`, `inputs/ClearancePolicy.lean`, `inputs/ClearanceAdmission.lean`, `inputs/ClearanceEntry.lean`, and `HandoffWitness.lean`. The exact script records hashes. C8's first sample is .316 s and dispatch .3165 s; its actual controller switches before the old braking polynomial's .325 s velocity zero. C8 proves a finite forward ceiling and already includes a finite terminal-box residual theorem. This review does not rebrand those as new discoveries or as standstill/PL evidence.

## Three transfers and their failure boundaries

1. **Viability and terminal sets.** Replace an event-only stop declaration by two tests on the same physical state: sufficient lower/upper clearance for the transient, then membership in an invariant terminal set that implies the requested residual tolerances. Preserve the original lag dynamics, saturation, rate interval, sensor age, global clock, and one-sided joins. A genuinely discriminating necessary test is the unavoidable retreat bound below. A sufficient existing-box adapter requires `L ≤ c−(51/50)K`, `c+(51/50)K ≤ U`, `εv ≥ (203/25)K`, and `εa ≥ (1616/25)K`, plus the actual source execution/entry theorem and a pre-entry travel certificate. Falsifier: a lower clearance below the necessary retreat buffer cannot work for the stated initial residual acceleration even with more favorable control than C8. Conversely, a negative box endpoint only defeats that sufficient abstraction; it does not prove an actual trajectory violation.

2. **Unexpected actuator-memory/impulse coordinate.** For a constant known lag rate, define `p=v+a/r`. Then `p'=b`, where `b=u+d` is the effective acceleration target. This borrows the momentum/impulse viewpoint but retains the actuator's stored acceleration, unlike kinetic energy `v²/2`. At `v=0,a=−6/5`, `p=−3/20` for r=8. Setting effective target to zero preserves this nonzero p and leaves a nonzero limiting velocity. Falsifier: applying the same invariant across varying rate is wrong; at a rate change 8→12 with unchanged physical state, p changes by 1/20. For differentiable varying rate the missing term is `−a r'/r²`; the original source does not bound r'. This is therefore a diagnostic coordinate and possible fixed-rate synthesis tool, not a universal certificate.

3. **Temporal contracts and transactional release.** Treat a maintained-stop assertion as a predicate on the original execution: for every real time in `[T,T+H]`, travel remains in `[L,U]` and residual `|v|,|a|` stay below declared tolerances; an infinite claim needs a compatible infinite execution. The runtime declaration must bind the actual entry state, controller, reading history and original clock, with enough latency margin. The positive adapter is the existing finite `sampled_variable_entry` theorem, only when its interval is nonempty and its tolerances are acceptable. Falsifiers: changing “for all times” to endpoint samples; restarting T at receipt while keeping an old age certificate; or replacing the future disturbance by zero. Persistent bounded disturbances may preclude arbitrarily tight rest, so a finite quiet tail is not an asymptotic theorem. Root's square-wave continuation is a useful discriminating test of this last boundary.

## Exact negative and positive tests

`inventor_terminal.py` uses rational arithmetic throughout the certificates and emits `inventor_terminal.json`.

* Counterfactual continuation of the **old braking input**: `x=.001+.39t−.6t²`, `v=.39−1.2t`, `a=−1.2`. At first zero `t=13/40`, `x=103/1600`; at t=.66, x=−37/12500. This is not the actual C8 continuation, which switches earlier.
* New ideal mode `b=0` beginning at that first-zero state, r=8: one second later `x=−107/1600−(3/160)exp(−8)<0` and the limiting velocity is −3/20. This is an explicitly changed post-mode; command u=0 with unknown d would not imply b=0.
* Exact vertices of the existing weighted target box K=9/200 give the sharp **box-abstraction** support bounds `|x−c|≤459/10000`, `|v|≤1827/5000`, `|a|≤1818/625`. These reproduce source residual bounds; vertices are not claimed reachable.
* Actual C8 sample632 yields c=2525673/100000000 and K=9/200. The same box gives `[−2064327/100000000,7115673/100000000]`. Thus it passes a declared lower limit −.03 and upper .15, but cannot certify a lower limit zero. An earlier-prefix lower bound and source theorem premises are still required for a full execution claim.
* With the unchanged hold feedback, exact readings, constant allowed d=±.01, the equilibrium offsets are ±1/800 with v=a=0 and unclipped u=∓.01. Thus both such equilibria cannot satisfy a position tolerance less than 1.25 mm around the fixed center. This is an equilibrium-family obstruction, not a claim those equilibria are the given C8 transient endpoints.

## New necessary retreat clearance

At a continuous-state instant with v=0 and a=−A<0, let the subsequent source actuator bounds hold: r∈[8,12], clipped u∈[−2,2], and |d|≤.01. Thus b≤B=201/100. Put `K=12(B+A)` and `τ=A/K`. For `s∈[0,τ]`, compare acceleration to `ā(s)=−A+Ks`.

At an upward crossing `a=ā`, we have `ā≥−A`, so

`a'=r(b−ā) ≤ r(B+A) ≤ 12(B+A)=ā'`.

Use an arbitrarily raised/strict barrier or the usual one-sided comparison argument. This does **not** assume actual acceleration stays above −A: it may dip below, which only makes an upward crossing test more necessary. Full-state continuity and the source one-sided derivative framework are needed through cell joins. Therefore `a≤ā`; integrating on the same trajectory twice gives

`x(τ)−x(0) ≤ −A τ²/2+K τ³/6 = −A³/(3K²)`.

For A=6/5, K=963/25, τ=10/321 seconds, the unavoidable retreat is at least **40/103041 m = .388194990… mm**. Therefore lower clearance below that amount is infeasible under these assumptions. This is conditional on the stated first-zero acceleration, not the unknown actual C8 first-zero state. It does not claim the bound is tight.

`inventor_retreat.lean` kernel-checks the general crossing-boundary inequality, exact polynomial-integration arithmetic and constants. All three lemmas use only propext/Classical.choice/Quot.sound. **The differential comparison and integrations themselves are not formalized in this file**: the second lemma explicitly assumes the already-integrated upper bound. `inventor_compile.py` uses the existing C8 pinned environment; log preserved. The complete analytic implication is a next formalization target, not a completed kernel theorem.

## Critique of the root numerical continuation

Read `pm_sampled_hold.py`: the previous sample at σ+n h correctly drives the cell starting at σ+(n+1)h; the original first reading, pending prefix, clamp ordering and physical target error are retained. Constant future rates and square-wave target errors are allowed new choices in the C8 family, not the literal saved three-cell witness. Grid extrema and an 80-second tail do not prove all-time extrema or a periodic limit. A stronger next test is the two-second sampled affine return map, a certified periodic orbit and a transient enclosure with clipping guards verified.

## Recommendation and quality

GO for a 30-minute source-bound adapter: formalize the retreat barrier for the actual one-sided execution and produce a terminal admission record that checks both travel sides, nonempty duration, actual residual tolerances and the original clock. Preserve explicit failed admissions. HOLD any precision-rest assertion until requested tolerances and persistent-disturbance treatment are fixed. NO-GO for “first zero implies maintained stop,” or for zero effective target as a general arrest strategy.

Evidence levels: source theorem inspection; exact rational arithmetic; three kernel-checked helper lemmas; analytic comparison argument with a named formalization gap; root simulation audited but not independently reproduced here. No physical validation, novelty claim, or standards certification. Rubric: provenance 4/4, distinct transfers 4/4, falsifiability 4/4, test strength 3/4, scope discipline 4/4 = **19/20** for this scoped inventor review. Subjective confidence: 95% in the analytic retreat implication, conditional on existence and one-sided comparison hypotheses; lower for full adapter completeness, which remains work.

## Completed supplement during the initial session

See `inventor_interval_audit.md` for the independent exact replay of the PM finite10.5-second witness and two successful semantic negative controls. The observed velocity enclosure is about .0022881462917086763m/s, strictly above .001. This replaces the earlier statement that root simulation was only read: the exact interval witness is now independently reproduced, though no infinite-limit or physical claim follows. The independent positive-exponential-series/direct-cell implementation initially failed from interval dependency; its failed version is preserved.

Retreat improvements are additive: the critic's linear-barrier minimum doubles the initial bound to80/103041m≈.776389981mm at20/321s. Root's exponential barrier yields the stronger analytic lower-clearance necessity1923/1600000m=1.201875mm at1/12s using exp(−1)>367/1000. All original lemmas remain; six helpers now compile with standard axioms. Updated Lean SHA256117438fbf74a9da47ef29442360af77f3beff158f9d701e2eb107e912314b5dd. The full differential comparison/integration bridge remains explicitly open; the exponential arithmetic lemma assumes its enclosure.
