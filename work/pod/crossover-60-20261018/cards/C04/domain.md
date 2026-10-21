# C04 domain review — preserve the actual clearance region

AI-assisted domain role; inherited root model, exact identifier unavailable. Root owns elapsed time and final decision. No original source, Challenge, execution, sensor bound, or controller file was modified.

## Source binding

Read the frozen roster, AGENTS.md, campaign CHARTER, AGE-BUDGET.txt, C3 REPORT.txt, C7 REPORT.txt and C7's copied DigitalHold.lean, AdaptiveAdmission.lean, ClearancePolicy.lean, ClearanceAdmission.lean and DelayedEntry.lean inputs. The old planning screen is superseded by actual finite constructed C7 hold executions at total information age1ms. The C7 model still has source-specific pending history, clipping before physical target error, distinct left/right command channels, fixed once-selected center, and delayed prior-sample use. None of those may be discarded when raising age.

Physical model: x'=v, v'=a, a'=r(u+d−a), r∈[8,12], |d|≤.01. Original gains(p,q,h)=(8,6,.5) give u=−p(x−c)−qv−ha. Sensor errors are (.001,.01,.05), clipping authority ±2. Pending target is−1.21 through startup D≤.5ms; it is retained on the left at D and replaced on the right. Source pending estimates include |v|≤.03066, |a|≤1.32.

Coordinates remain z=(x−c,x−c+v/4,x−c+v/2+a/16). The outer cube radius is R=2221/40000=.055525. But **C7's declared clearance uses the narrower weighted region** |z_i|≤weight_i*K, weights=(1.02,1.01,1), with K=ClearancePolicy.policyRadius(m)∈[.045,2407079/50250000]. Center is the source's fixed clearance policy. Nominal c=.09573033 and weighted ceiling=.14163033; c+R=.15125533 exceeds .15. Preserving only the outer cube does not preserve C7's clearance statement.

## Exact general-gain derivation

Let B=(−p+4q−16h,−4q+32h,−16h), so u=B·z. The first two transformed rows are unchanged: z0'=4(−z0+z1), z1'=4(−z1+z2). The third row is A·z+r*w/16, with total digital mismatch w=u(read)+d−u(actual), and

A=(4+r(B0−16)/16, −12+r(B1+32)/16, 8+r(B2−16)/16).

For a fixed weighted box with radii d_i*K, its exact third-face feasibility condition is

|A0|*d0*K+|A1|*d1*K+A2*d2*K+r*W/16≤0.

The first two faces point inward for descending positive weights. Since the absolute-affine row bound is convex in r, endpoint tests at8 and12 suffice; the accepted candidate also has a direct all-real-rate Lean proof, rather than assuming rates take endpoint values.

The command derivative has coefficients
C=(4p−16q−hr(B0−16), −4p+32q−hr(B1+32), −16q−hr(B2−16))
and mismatch coefficient−hr. Thus exact robust slope is max over r endpoints of K*Σ|C_i|d_i+|h|rW. Measurement cost is |p|*.001+|q|*.01+|h|*.05. Authority follows from K*Σ|B_i|d_i plus measurement cost.

## What failed and what improves

With unchanged gains, the outer cube can tolerate W≤8R/3, rather than the old sufficient2R. However the actual weighted region only permits W≤(38/15)K: at K=.045 this is.114. Raising W to.234 with old gains produces outward derivative.09 at the exact r12 upper weighted face. This is a counterexample to that robust-face certificate, not a realized unsafe sampled trajectory.

The PM proposed p=16/3,q=6,h=.5. Independent derivation confirms that it changes A0 from4−r/2 to4−r/3, making both off-diagonal coefficients nonnegative on[8,12]. This avoids the old absolute-value penalty. The exact weighted mismatch threshold becomes

W≤(394/75)K; at K=.045 this is.2364.

All coordinates, weights, center policy, sensors, pending command, initial-state estimates and authority are retained. The digital command changes after dispatch as explicitly authorized by gain co-design. There is no physical-history reset.

For these gains, command norm≤(674/25)K=26.96K, sensor-plus-physical cost M=301/3000≈.1003333, and the digital slope bound is

max((9736/75)K+4W, (8884/75)K+6W).

The retuned pending feedback slope remains≤8 under the source pending-state bounds. This was separately proved from the unchanged old pending dynamics; it is not borrowed from a digital mismatch premise.

## Noncircular finite two-pass candidate at16ms

On a hypothetical first-contact weighted-box prefix, start with the coarse bound from two independently bounded commands:

W0=(1348/25)K+M.
L0=(33148/75)K+6M, which bounds both endpoint digital slopes and the pending slope8 for every K≥.045.
W1=M+.016L0.
L1=max(8,(9736/75)K+4W1,(8884/75)K+6W1).
W2=M+.016L1.

Lean proves **W2<(394/75)K for every K≥.045**, not merely a three-point numerical screen. At K=.045, L1=8 and W2=137/600≈.2283333, leaving slack121/15000≈.0080667. Authority remains strictly below2 throughout any inflated first-contact box K≤.05. The source policy's largest K is below.05.

This algebra includes the pending interval in both passes through max8. It does not pretend that an old stamp is fresh at dispatch. Total information age16ms is not the same as a16ms sample period: a one-cell prior-reading architecture can incur almost two cell periods. Any constructor extension must preserve startup D separately and prove its actual timestamps, including the first digital cell.

## Original shrinking-envelope contract

The static weighted-region argument above does not automatically preserve the source shrinking envelope: old readings may come from the larger earlier region. The PM selected a15ms three-pass route producing one fixed history-wide residual below.23. `domain_shrink.lean` proves, for every K≥.045 and all real r∈[8,12], that |w|≤.23 makes every weighted face decrease at the original speed delta=3/1700: first face≤−1.02delta, second≤−1.01delta, third≤−delta, with symmetric lower faces. At K=.045 the first face is exactly tight; the third has the stronger margin−.0038. This preserves the source shrinking-face conditions if the mixed-history execution bridge is assembled. It does not infer the historical residual from the current, smaller radius.

## Artifacts and evidence

Standalone proofs use the existing ctrl pinned Lean environment; no C7 dependency source was edited. Producer commands are `lake env lean ../work/pod/crossover-60-20261018/cards/C04/domain_<name>.lean` from `/Users/mike/Dev/ctrl/lean`.

- domain_faces.lean:7 declarations, general-gain coordinate/slope identities; baseline weighted faces and sharp necessity; outer-cube necessity; exact clearance numbers.
- domain_codesign.lean:6 declarations, retuned weighted faces and sharp threshold; slope, command and measurement arithmetic.
- domain_budget.lean:3 declarations, universal K two-pass16ms budget, authority, nominal slack.
- domain_slope.lean:2 declarations, retained pending slope and digital slope for every real r∈[8,12]. One harmless unused-variable warning.
- domain_shrink.lean:4 declarations, all six original weighted shrinking faces under fixed residual.23, with explicit stronger last-face margin.

All22 producer declarations compiled with only propext, Classical.choice, Quot.sound. Files are frozen for independent critic replay; consult critic-owned logs for final replay acceptance. These are algebraic/face bounds, not a completed increased-age execution theorem.

`domain_exact.py` independently reconstructs physical and transformed derivatives using Fraction, with no producer imports. It checks96 vertices at K=.045, the policy maximum, and.05; confirms exact slope/command maxima; checks1,16,18ms two-pass budgets; and reproduces the old-gain outward-face negative control. It passes ruff and writes domain_exact_results.json. The initial ruff missing-strict-zip warnings were fixed explicitly; arithmetic already passed before that cleanup.

## Remaining proof bridge and decision recommendation

Recommend **GO** for the PM-selected retuned15ms candidate preserving the full shrinking contract. The16ms static-region budget remains a separate algebraic lead, not an already assembled shrinking-execution theorem. Next, introduce an isolated age-parameter execution contract with precisely the original pending/startup/sensor/left-right semantics and retuned post-dispatch command. Port the source age-bound and first-contact argument using these checked bounds, and construct a nonempty causal continuation on the new timestamp grid. Existing source Execution fields hardcode1ms, so they cannot be cited as already accepting16ms.

The barrier must keep the weighted policy radius and center fixed, use a small epsilon inflation bounded by.05, derive the two-pass residual only on the first-contact prefix, and then discharge that prefix assumption. Existence and actual timestamp binding are separate from the face arithmetic. The original full clearance theorem is therefore **HOLD for extension**, not already proved at16ms. No robot, contact, noise distribution, precision-rest or hardware result is claimed.

Quality:18/20=90% (A−): faithfulness4, reproducibility4, discriminatory value4, critique3, actionability3; full execution integration remains missing. Subjective confidence95% in the candidate algebra and scope, not a calibrated probability of physical safety. PM owns the final campaign grade and decision.
