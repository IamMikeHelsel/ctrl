# C04 cross-discipline inventor

AI-written review; inherited root model, exact identifier unavailable. Only inventor campaign artifacts changed. Numerical optimization proposes gains; exact rational arithmetic checks the proposed finite inequalities. No source theorem, controller implementation, hardware or approved challenge was changed.

## Question and binding

Can the fixed digital-hold controller tolerate materially larger total information age without widening its declared clearance tube? Distinguish two answers: a sharper certificate for unchanged gains, and a separately labeled new controller. Neither can replace the established execution theorem merely because finite arithmetic passes.

Read the three frozen sources in CARD.md: AGE-BUDGET.txt, adaptive-admission-03/REPORT.txt and constructive-hold-07/REPORT.txt. Also inspected the C7 copied sources `inputs/WeightedEntry.lean`, `inputs/AdaptiveAdmission.lean`, `inputs/ClearanceAdmission.lean` and `inputs/ClearancePolicy.lean` under the same method-transfer-01/controls directory. The later C5/C7 clearance argument uses fixed center policy and weighted envelope, not just the old uniform cube. Its weights are(51/50,101/100,1), target9/200 and inward drift3/1700. The old uniform transformed radius is2221/40000. Preserving that larger uniform cube alone does not preserve the weighted clearance/entry argument.

There was a caught source-binding failure: the first inventor pending-slope calculation reused C3 startup bounds|a|≤1.30 and|v|≤.03065. Actual C5 `ClearanceAdmission.startup_acceleration` and `startup_velocity` use33/25=1.32 and1533/50000=.03066. Root and critic flagged it. The failed script and JSON are preserved as `inventor_mixed_wrong_startup.py.txt` and `.json`. Current calculations use the C5 bounds; the new-gain pending slope rises from7.64347 to7.68352. Acceptance survives because the subsequent holding bounds dominate the three selected refinement passes. No old failure was silently relabeled as a passing source-bound result.

## Three transfers

**1. Robust linear programming and positive-system geometry.** Keep the coordinate transformation, radius, center policy, weighted envelope and sensor box fixed. With acceleration gain fixed at1/2, the transformed face inequalities and feedback-slope vertex constraints are affine in position gainp, velocity gainq, mismatch budgetW and slope boundS. At a prescribed ageh, maximizingW−measurementCost−hS is a small linear program. A solver result is only a proposal; exact source-derived corner inequalities decide whether that proposal is accepted.

The proposed gains(p,q,h_a)=(16/3,6,1/2) produce

z3'=(4−r/3)z1+(−12+3r/2)z2+(8−3r/2)z3+(r/16)w.

Both off-diagonal coefficients are nonnegative for8≤r≤12. The invariant box face therefore avoids the old adverse sign contribution. This is a sign-structure change in the dynamics, not simply reducing a feedback slope. Sensor cost falls from.093 to271/3000≈.090333, while some conditional feedback-slope bounds increase. The trade improves the available mismatch margin despite that increase.

Preserved: the physical state, coordinate map, tube geometry, center, original pending command−1.21 and sensor/error boxes. Changed: feedback gains and therefore every actual held command after dispatch. A gain change must be reflected in execution, clipping, mismatch, derivatives and recurrence proofs. Falsifiers include trusting the LP objective, reusing old derivative lemmas, or claiming the new controller answers the unchanged-controller question by itself.

**2. Small-gain feedback as a finite refinement sequence.** A prefix cube gives a coarse command-difference bound without assuming a mismatch invariant. Integrating a slope bound improves that mismatch estimate; reuse the improvement for another finite pass. This is a monotone scalar information loop, not an assumption that its fixed point already holds. For the new gains and correct mixed history,

T_h(W)=271/3000+1/100+h max(7.68352,128R+4W,(352/3)R+6W).

At15ms its largest scalar feedback multiplier is.09. This explains why repeated finite passes tighten rapidly. The argument still needs the source's continuous state, one-sided command derivatives, actual retained reading timestamp, prefix bounds and first-contact proof. A reset at dispatch does not reset the age of an old reading. Falsifiers include omitting pending history, using the desiredW in the initial slope without deriving it, or checking only the old cube while changing the weighted clearance envelope.

**3. Unexpected transfer: a command-variation reservoir.** Replace a blind elapsed-time allowance by a conservatively certified accumulated command variation from the actual reading stamp: E(t)≥∫|k'(u)|du. Then measurementCost+physicalError+E(t)≤W is the same mismatch invariant. This resembles a resource accounting or energy-tank rule, but E is command variation, not physical energy; no passivity theorem is imported. It could permit long holds when feedback is nearly constant while rejecting short holds during rapid dynamics.

The hard missing bridge is causal access to a trustworthy upper bound on E. One cannot observe the actual continuous state for free or assume future feedback stays flat. A model-based reachable bound or suitably certified additional measurement is needed. The existing fixed-age rule remains a sufficient fallback using E≤S·age.

The exact bookkeeping negative control uses slope8, reading stamp0, dispatch.5ms and evaluation1.25ms. With variation allowance.008, resetting E at dispatch reports.006 and passes; the actual stamp-to-now variation is.01 and fails. This is an abstract counterexample to the accounting rule, not a demonstrated trajectory of the original plant. No new schedule or event-triggered safety claim is made.

## Exact tests

`inventor_codesign.py` tests fixed acceleration gain1/2 and ages10,20,30,40,50ms using SciPy's LP, then reconstructs rational gains and checks32 face/slope/authority inequalities. The proposed gains are16/3,6,1/2 in those runs. Old-uniform-cube mismatch budget2221/7500 and slope15547/1875 pass the10/20ms conditional age arithmetic; the same proposals fail30/40/50ms. The failed cases are preserved. They are not proofs that all gains fail at those ages: no exact optimality dual was produced.

The baseline uniform cube's true mismatch limit is8R/3, rather than the sufficient2R used by the older theorem. Its slope is max(96R+4W,80R+6W), so the purely uniform-cube conditional age ceiling is169/22210≈7.609ms with physical error.01. **This is not a same-clearance result**: the later weighted envelope has a smaller mismatch allowance.

`inventor_mixed.py` performs a pure-Fraction acceptance using the actual C5 weights and startup bounds. For the new gains:

- Pending feedback-slope maximum7.68352, checked over all endpoint vertices.
- Measured command magnitude≤1571/1000, hence clipping is inactive under the prefix cube with margin429/1000.
- Initial non-age mismatch bound1837/600.
- At15ms, three finite refinements give respectively710411/1500000,36102299/150000000 and1660366897/7500000000≈.221382253.
- Uniform-cube allowance2221/7500≈.296133 remains strict.
- The same weighted envelope and inward drift allow at most9947/42500≈.234047059. The derived residual has margin1614762751/127500000000≈.012664806.
- All24 weighted face vertices pass at targetK=.045; their row coefficients are negative, so increasingK preserves the inward inequalities. The unchanged first-coordinate face reaches equality at the target; the source-style inflated first-contact proof remains necessary.

There is also a useful **unchanged-gain** result. With gains8,6,1/2, the correct startup vertex maximum is7.76528 rather than the rounded8. At age1.1ms the coarse mismatch2.7682 tightens in two passes to.111541808. This is below the unchanged weighted-envelope allowance≈.111647059 by≈.000105251. Thus a modest10% age increase survives exact algebra with the same gains, center and clearance geometry. This should be the first same-controller formalization target. It is a numerical constant improvement, not a claim of material hardware benefit.

A stronger subsequent unchanged-gain test keeps the weighted prefix directly, using `ClearancePolicy.radius_upper`: Kmax=2407079/50250000. Its measured-command bound is24.24Kmax+.093, below2. The holding slope becomes S(W)=max(97.28Kmax+4W,80.48Kmax+6W). The actual pending interval lasts at mostD=.5ms, so its contribution to any sample-to-now interval of ageA is bounded by

S(W)A+max(0,7.76528−S(W))min(A,D).

This charges the original reading history and does not reset a timer at dispatch. `inventor_baseline_weighted.py` obtains, atA=1.4ms, residuals.1287696776,.1115401328,.1114781065 over three passes. The final residual is below the same weighted cap by≈.000168952. This is the stronger **40% fixed-law age-increase candidate**, superseding1.1ms as the next formalization target. At1.5ms, an affine lower-map fixed point already exceeds the weighted cap; no number of these particular coarse-bound refinements can repair that case. This diagnoses a sufficient-proof limitation, not an unsafe trajectory. The weighted-prefix hypothesis still needs a faithful first-contact discharge; source `radius_upper` alone does not prove the future prefix remains inside it.

## Decision and limits

GO first for a source-bound theorem at1.4ms with unchanged gains and geometry, using the weighted prefix and actual pending duration. GO separately for a declared new-gain15ms controller using the same weighted envelope, after replacing the affected command/derivative/clock proofs and constructing an admitted execution. The latter is a substantial algebraic opportunity, not an already certified operating limit. The old center policy and pending command must remain bound through that rewrite.

HOLD the variation-reservoir policy until a causal computable bound and full timestamp contract exist. NO-GO for presenting the uniform-cube7.609ms ceiling or LP20ms candidate as preservation of C7 clearance, for resetting history at dispatch, or for treating a solver's optimum as a proof.

Evidence is exact finite rational verification plus the inspected source contracts. No new Lean theorem, global existence theorem, physical simulation or hardware acceptance is claimed by this role. All current inventor Python scripts pass Ruff; the failed source-bound attempt remains archived. Quality: faithfulness3/4, reproducibility4/4, discriminatory value4/4, critique4/4, actionability4/4 =19/20 (95%). Subjective confidence is high in the corrected algebra; the full larger-age execution and clearance proof remain to be constructed.
