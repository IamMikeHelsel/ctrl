# V01 — Faithful projective plane transfer

**PM: GO. Quality95/100 (19/20).** AI-written four-role initial review. Actual elapsed substantive time is in state.json. Reused domain/inventor/critic plus root PM, inherited working model with exact runtime ID unavailable; no Spark or alternate-model inference claimed.

Question: Under explicit nonzero-ray, depth and invertibility conditions, which projective incidences and plane-induced image constraints survive a camera-frame change?

## Provenance and prior result

- /Users/mike/Dev/ctrl-research-notebook/ControlsLean/Vision/Homography.lean
- /Users/mike/Dev/ctrl-research-notebook/docs/proposals/01_planar_homography.md

Prior investigated source proves vector incidence, determinant and plane-motion identities over an arbitrary field. Those are valid algebraic results; they do not alone implement a nonzero projective quotient or physical calibrated camera. Source and approved challenges unchanged. Byte-identical Epipolar/Homography copies freshly compile under available Lean4.33. Original pin4.36 compiler is installed, but its compiled Mathlib cache is unavailable: **pinned4.36 validation remains unperformed**.

## Creative transfers and discriminating evidence

1. **Control refinement → admissible camera relation.** Retain plane equation, exact motion, depths, ray/line nonzero, inverse, calibration and optical-axis conventions as explicit premises. Domain15 source-importing lemmas derive first-ray/depth/normal nonzero, second-ray/depth nonzero under inverseH, nonzero scaled-ray relation, representative equivalence, line nonzero, calibratedpixelK2HK1inv and determinant criterion. ForRy=t, detH=detR(1+n·y/d); with invertibleR, singularity is exactly camera2center−y lying on the plane. Source algebra does not need Rproper or unitn; physical readings do.
2. **Robotics coordinate types → faithful frame transport.** Transport points and camera centers, vectors, plane covectors, opticalaxes and intrinsics consistently. Passive translation cancels in X−C; translating a point and normalizing it without movingC changes the pixel. Joint scaling of(n,d) preserves the plane; scaling onlyn does not. Passive orthogonal basis change preserves physicaldepth when opticalaxis is also transported; active motion may put a ray behind the camera. Exact fixtures distinguish these operations.
3. **Unexpected transfer: orientation cover and partial charts.** Sign-projective equality identifies x and−x, but their visibility differs. A generic Lean obstruction says a sign-invariant predicate cannot equal positive opticaldepth. Known estimatedHscalealpha restores physicalheight throughq3/alpha. InvertibleH can send a finite ray to the chart horizon; recharting repairs coordinates, not camera visibility. Linezero-set incidence likewise does not determine the orientation of a halfspace.
4. **Numerical robustness → guarded quotient contract.** Exact known-camera patch has detH6/5 and positiveheight[2/5,6/5]. Homogeneous incidence pairing survives, while equal rawsource residualmagnitudes1/2 become5/12 and5/4 after normalization. Correct absolute-residual threshold is divided by|height|. Third-row perturbations≤.001 give height≥1593/4000 only. Under the stronger all9entry fixed-gauge perturbation bound, exact quotient analysis yields coordinateerrors≤28/1593 and49/6372;2048corner tests include a witness attaining both. Universal bound is proved by row-error/quotient inequalities, not inferred solely from sampling. Nine exact calibration cases verifyK2HK1inv; omitting calibration fails.

## Independent critique and evidence boundary

A properR and positive depths for observed points still allow singularH: R=I,t=−e1,planeX1=1 collapses two distinct visible inputrays to one outputray. Domain's81rational tests include12singular cases; critic independently checks the physical collapse and source bindings. Zero rays/lines, d0, zero seconddepth, horizons, wrongline action, calibration omission, signgauge and inconsistent axis/plane transport have explicit negative controls.

The proposal's statement that epipolar geometry applies only to noncoplanar scenes is false. The [authors' epipolar chapter](https://robots.ox.ac.uk/~vgg/hzbook/hzbook2/HZepipolar.pdf), pp239–243, confirms scene-independent epipolar geometry and plane transfer excluding both centers. Critic verifies nine physical planar epipolar pairs and rejects a wrongpair. Uncalibrated F=[e′]×H ambiguity must not be treated as an arbitrary family of calibrated essential matrices. No source prose was silently repaired.

`critic_acceptance.json` is the authoritative independent Lean acceptance ledger; pending or failed drafts are excluded. Accepted declarations use standard permitted axioms. Generic division identities are algebraically total at zero, but a usable pixel chart requires nonzero/positiveheight separately. Current exact/kernel/hand results do not establish actual calibration, uncertainty estimation, global physicalvisibility, occlusion, full quotient packaging, fixed-pin rebuild or hardware validation. Classical projective facts are not claimed novel.

## PM decision and next action

GO for the faithful camera-contract layer. After all60 initial reviews, spend30minutes building one source/coordinate/gauge/calibration/plane/depth/uncertainty-manifest consumer, with20 predeclared semantic mutations from next_block_protocol.json. It must admit the exact positive fixture, reject singular/zero/stale/convention failures, and distinguish unsigned incidence, oriented visibility and metric thresholds. Keep originalpinnedbuild and measured-camera interface as named HOLD obligations; do not repair them by weakening the camera statement.

Quality rubric: faithfulness4/4, reproducibility4/4, discriminatory value4/4, independent critique4/4, actionability3/4. Subjective confidence high in scoped exact/kernel evidence, uncalibrated for deployment or empirical utility.
