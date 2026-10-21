# S11 domain review: a stop event is not maintained rest

AI-assisted domain researcher; inherited root model, exact identifier unavailable. Root owns the timed review and PM decision. Original sources and approved challenges are unchanged.

The frozen question asks what extra controller/contract is needed for two-sided travel and explicit residual-motion tolerances after a finite first-zero maneuver. Source reports are C8 constructed-handoff-08, milestone-01, and performance-level-review in the frozen roster. I inspected the actual C8 input modules DigitalHold.lean, WeightedEntry.lean and ClearancePolicy.lean under `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-18/method-transfer-01/controls/constructed-handoff-08/inputs/`.

## What the accepted source actually supplies

The C8 construction links the original recovery/detector path through pending arrival to a finite C7 sampled hold. It supplies a forward ceiling, not a complete two-sided travel or rest contract. C6 has an upper initial-position bound but no absolute lower initial-position bound. Translation of the admitted initial state therefore prevents inferring a universal lower travel limit for the full prefix.

The unchanged holding feedback is `u=clip[-8(x-c)-6v-a/2]`, clipped at±2, then physical target error is added. The actuator rate lies in[8,12]. The digital contract allows total information age≤1ms, sensor errors(1mm,.01m/s,.05m/s²), and physical target error≤.01m/s². Tilted coordinates are

`z=(x-c, x-c+v/4, x-c+v/2+a/16)`.

The initial invariant cube radius is2221/40000m=.055525m. WeightedEntry uses weights(1.02,1.01,1), targetK=.045, and certified entry time7157/1200s≈5.964s. At its plateau it guarantees only |x-c|≤.0459m, |v|≤.3654m/s, |a|≤2.9088m/s². These are useful bounded-motion statements but are far from small residual motion. No physical reliability or standard-compliance inference is drawn from them.

The C8 admitted braking witness is `x=.001+.39t-.6t²,v=.39-1.2t,a=-1.2`. Its first velocity zero is t13/40s, at x103/1600m. If this same braking law continues, x(2/3)=−17/3000m<0. This is an exact counterexample to treating that first zero as a maintained stop with illustrative lower limit0. It is a continuation of the source braking law, not the switched C8 hold trajectory.

## Terminal contract and exact center admission

A residual-motion requirement must name position bounds[L,U], velocity toleranceVtol, acceleration toleranceAtol, arrival deadline, and hold duration. A center-relative band alone does not certify travel from an unknown absolute starting position. A finite dwell observation alone does not guarantee future rest under arbitrary later admitted forcing.

For the original weighted box |z_i|≤weight_i*K, exact physical bounds are

```
|x-c| ≤ (51/50)K
|v|   ≤ (203/25)K
|a|   ≤ (1616/25)K
|u_continuous| ≤ (606/25)K.
```

Consequently a sufficient tolerance certificate requires(203/25)K≤Vtol and(1616/25)K≤Atol, plus center reserve `L+(51/50)K≤c≤U-(51/50)K`. This is a conditional terminal-box implication; it does not establish reachability or invariance of an arbitrarily reduced K.

The C5 propagated observation intervals already encode pending/sensor uncertainty. Let offsets be `(mx,mx+mv/4,mx+mv/2+ma/16)` and errors the unchanged C5 vector `(101533,368033,1042283)/100000000`. For a declared K, robust entry requires each interval to fit its weighted box. The full center intersection is

`c ∈ [L+1.02K,U-1.02K] ∩ ⋂_i [offset_i+error_i-weight_i*K, offset_i-error_i+weight_i*K]`.

The theorem `exists_center_iff` proves exact existence by taking the maximum of all lower endpoints and checking it against every upper endpoint. `two_sided_terminal` then binds the resulting physical-position reserve to the ACTUAL source coordinates. This is the reusable admission test, not a sampled optimization.

Changing the selected center changes the future command. The original C8 assembly is instantiated at its own `center(m)` and cannot be reused unchanged for a different candidate. A new center requires rebuilding/generalizing the future C7/C8 execution and entry bridge. Alternatively, add a lower-clearance guard that accepts the existing source center only when it already meets both sides. The entire old recovery prefix separately needs an initial lower-position assumption and a lower travel proof.

## Why merely shrinking the old box fails

Current policyK≥.045 cannot certify1mm/s via its box projection. More sharply, the unchanged transformed third upper face at r12 and z=(-1.02K,+1.01K,+K) equals

`z3' = -(19/10)K + (3/4)W`.

For the COMPLETE weighted box to remain invariant under an independent residual bound |w|≤W, this admissible face requires W≤(38/15)K. Coupled with its1mm/s speed certificate, K≤1/8120, this requiresW≤19/60900≈.000312m/s². Even the physical target uncertainty.01m/s² alone exceeds that budget. Smaller age or a smaller nominal radius cannot fix this face while retaining the same disturbance contract and whole-box geometry.

This is a certificate/facet obstruction, not an impossibility theorem for every controller, correlated residual set, or terminal-set shape. A useful next design could reduce justified uncertainty, use a different invariant geometry, or add a load-holding mechanism with its own physical model. None is silently assumed here.

## Persistent motion permitted by the broad C5 contract

An additional mathematical warning is available without changing the feedback law. Take fixedr8 and `x=c+A sin(4t)`, with A3/10000m. Then velocity peaks1.2mm/s forever. With exact sampled readings and age≤1ms, the required target error is

`d=a'/8-u_held+a`.

For instantaneous feedback its magnitude is≤32A; command slope magnitude is≤160A, so holding adds≤160A/1000. Hence|d|≤.009648<.01, and commands remain inside±2. This gives a conditional persistent-motion construction in the BROAD C5 Execution channel when its sinusoidal forcing and sampling correspondence are supplied. It is ordinary derivation, not a checked complete execution theorem.

Crucial limitation: C7's constructed future target errors are constant within each cell. The sinusoidal d above is not such an exact C7 recurrence witness. Do not promote it as a counterexample to that narrower construction. The independent residual-face obstruction and source braking continuation remain exact regardless of this distinction.

## Checked artifacts and interpretation

`domain_terminal.lean`: six checked declarations importing actual ClearancePolicy/DigitalHold definitions, including physical tolerances, exact existential center intersection, two-sided terminal containment, current floor failure and continued source-braking arithmetic.

`domain_face.lean`: four checked source-bound declarations for the exact upper face, necessary residual budget,1mm/s consequence and comparison with physical uncertainty.

Both compile in the original C8 pinned Lean environment using the existing compiled dependency closure. All ten printed closures use only propext, Classical.choice, Quot.sound. This is not a fresh rebuild of all original sources. `domain_compile.py` reproduces the terminal module and passes scoped Ruff checks. The full future execution, infinite hold, reachability, and new-center trajectory are not asserted by these helper proofs.

Recommended decision: GO for a stated two-sided terminal admission contract and a source-bound small-terminal-set design; HOLD any maintained-rest claim until the tolerances, deadline/hold horizon, lower starting clearance, and residual/actuation contract are fixed and proved. NO-GO for equating firstzero, a large invariant cube, or an observed dwell with future standstill.

Next discriminating test: select explicitVtol/Atol, compute the exact feasible observation/center region, then either find a robust inward terminal-set certificate under the unchanged uncertainty bounds or present an admissible residual witness excluding it. Preserve state and command history through the handoff.

Quality rubric: faithfulness4/4, reproducibility4/4, discrimination4/4, critique4/4, actionability3/4=19/20 (95%). Subjective confidence in the checked algebra and stated scope:95%. The policy/reachability bridge remains open.

## Final initial-review supplements

The critic found a stronger obstruction at the ACTUAL source reading. `domain_obstruction.lean` imports HandoffWitness and proves

`oldReads 632 = (10051/156250,27/2500,−6/5)`.

Its third offset minus propagated error equals−1569643/100000000. For everyK≥0, fitting the source third observation interval requires `c≤K−.01569643`, whereas lower-limit0 reserve requires `c≥1.02K`. These are incompatible. The checked theorem quantifies over everyK andc; it excludes this entire box-based lower-limit certificate at the source event. It does NOT prove the actual trajectory crosses zero or rule out a less conservative reachable set. This also makes explicit why changing only the center is insufficient at this source reading.

A positive arithmetic design point is available if the implementation contract is explicitly strengthened. Keep the original gains and weights but chooseK=1/8120. Required new uncertainty limits are physical target error≤10^-4m/s², sensor errors(10^-6m,10^-5m/s,10^-4m/s²), and total information age≤1/2000s. These are prospective specifications, not measured hardware facts and not the old C5 contract. Every retained sample state must already lie in the same terminal box; old history cannot be reset or assumed away.

Then V=1/1000m/s, A=202/25375m/s², U=303/101500m/s² and the instantaneous sensor-plus-physical residual isM=109/500000. A first-contact argument would initially bound residual byW0=2U+M. The unchanged continuous command derivative satisfies `|u'|≤8V+12A+6U+6W0`, yieldingL0=8047381/50750000. Age refinement gives

`W1=M+L0/2000=30174381/101500000000 < 3/10000 < 19/60900=(38/15)K`.

The third face is strictly inward for everyr∈[8,12]; the first two weighted faces have margin.04K. Command plus sensor error remains well inside clipping. `domain_small_budget.lean` checks the exact budget and third-face endpoint margin; it does not prove the whole first-contact argument, construct a new digital execution, or establish reachability from the old C8 state. The remaining settling phase and retained-history flush/admission are substantive open obligations. This design point specifies a falsifiable resource requirement for a useful terminal set rather than changing the old theorem's uncertainty silently.

These two extra modules add four printed declarations with standard axioms. Total domain checked helper declarations:14. A harmless unused-lower-rate-variable linter warning remains in the algebraic third-face lemma, which needs only the upper bound; no proof placeholder or added axiom is present.

`domain_small_faces.lean` closes the geometric part of the prospective design: for everyr∈[8,12], |w|≤.0003, and every point of the source-weighted K1/8120 box, each of its six actual transformed-vector-field faces points strictly inward. The single printed theorem compiles with standard axioms. Total domain helper declarations:15. Discharging the digital residual along a retained-history trajectory and proving entry remain separate.
