# R12 — Coupled Franka tracking and total actuation

**PM decision: GO for a bounded contract experiment; physical transfer remains HOLD.** AI-written research, four roles, inherited root model with exact runtime identity unavailable. Initial review time is recorded in state.json; preparation and interrupted gaps are excluded.

## Original question and provenance

What explicit coupled tracking and total-actuation contract could justify transferring scalar checked references to the recorded FR3 simulation or a specified physical Franka arm?

Frozen source: `/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/franka-demo-08/README.txt`, SHA256 `2d4eb89f2f3e9806a806cc2ef4ea29cd70f88fde2911681dec0b34baf2c07adb`. Source binding, original script, protocol, model manifest, dependency lock and all sixteen traces were inspected. All128 model-file hashes match Menagerie FR3 commit62ab00f2bc44f6f20c1c9b7a13f3fb1dd41a4e35. The existing MuJoCo3.16.0 runtime was used without installation.

Prior work provided scalar reference certificates and a disclosed model-only smoke demonstration. The model task moves joint1 with other joints commanded home; its task output is world attachment-site position, not orientation or a Cartesian straight line. Its0.2mm criterion applies to the final1.8–2s window, not a transient tube. Physical Franka variant, payload, firmware and execution interface remain unspecified.

## Creative transfers and preserved assumptions

1. **Controls to robot refinement:** expose the full coupled error equation before transferring scalar bounds. For e=q−qd, raw servo Kp(u−q)−Kv qdot, delivered-minus-raw clamp discrepancy Δτ, the residual is `(assist−bias)+passive+constraint−M qd_ddot−Kv qd_dot+Kp(u−qd)+Δτ`. Full inertia, original reference, retained history, timestamps and force mapping are preserved. Uniform residual/coercivity bounds and runtime binding are still missing.
2. **Thermodynamic accounting as a surprising falsifier:** a motion can do zero mechanical work while requiring sustained holding torque. Assisted hold has approximately26Nm bias and2083.407Nm²s squared-torque duty over2s, yet zero work. This rejects work as a replacement for force or thermal limits. Squared torque is only a duty proxy without motor/thermal parameters.
3. **Hybrid systems and bounded variation:** a smooth reference emitted as a1kHz staircase does not confer ordinary finite command jerk. The original queued reference has exact hold allowance1/5000rad and an explicit nonzero command jump. A lead changes the appropriate hold budget. Analytic-reference, command, physical trajectory and sampled derivative claims must remain separate.

## Discriminating tests and independent reproduction

All32,016 original rows were reconstructed independently. Raw actuator, delivered generalized actuator, bias and flange position match exactly. No saved original row exceeds the model total-force comparison limit: worst summed-force/limit ratio0.3059797704. The XML limits joint actuator force, while ideal bias is added outside that clamp. A changed-command negative at home produces raw−2250Nm, delivered−87Nm and bias−25.999663Nm, totaling−112.999663Nm. This is an explicit architectural counterexample, not an original-run failure or physical motor limit. Gear-two mutation rejects equating raw force with generalized torque without transmission binding.

At the worst original queued assisted state, `−0.1 qd_dot1` predicts0.016326785rad lag versus actual0.016594713rad. All source gains have Kv/Kp=0.1s. The velocity-forcing term is73.47Nm versus1.545Nm inertial reference forcing; these are error-equation terms, not actual torque requirements. Kinematic coordinate replacement attributes9.201654mm of the9.212598mm error to joint1, with0.010955mm from the other joints. This diagnostic does not resimulate altered dynamics.

Root tested the causal command `u1=qd1+0.1 qd_dot1`, keeping original reference/goal scoring, gains, histories, limits and assistance. Zero-lead baselines reproduce both original integration-step arrays bit-for-bit. Independent critic implementation shares only the original reference evaluator and reproduces the complete0.5ms lead array bit-for-bit.

| Metric,0.5ms integration and1ms logging | Original assisted | Velocity lead |
| --- | ---: | ---: |
| Peak original-reference tracking error |9.212598mm|0.333647mm|
| Final-window goal error |0.112452mm|0.003097mm|
| Peak goal error |29.988553mm|31.954445mm|
| Peak speed |0.162856rad/s|0.201754rad/s|
| Sampled jerk |135.229514rad/s³|147.989117rad/s³|
| Maximum total-force/limit ratio |0.299118|0.299273|

At1ms integration lead peak tracking is0.298351mm. Integration-step agreement is diagnostic, not an enclosure. Removing ideal bias assistance yields6.053464mm final-window error, independently reproduced bit-for-bit, failing the actual source criterion. Thus the lead supports the mechanism but cannot substitute for bias compensation or establish a uniform0.2mm tube.

Nine declarations in `domain_contract.lean` were independently compiled by producer, critic and PM with only propext, Classical.choice and Quot.sound. They prove conditional coercivity, signed total-force intervals, reserve sufficiency, clamp-aware residual identities, lead cancellation, source gain ratios and task-budget algebra. They do not prove the physical or simulated closed-loop tube. Exact small coupled-matrix, geometry and sampling countermodels reject missing assumptions.

## Explicit contract still needed

Bind model/variant, payload, frames, transmissions, actuator and total-force/rate limits, sampling/transport and authoritative retained history. Establish uniform inertia coercivity and a complete residual bound over an invariant region. A sufficient hand-derived route uses one common Lyapunov matrix P for the full coupled error dynamics, bounds on PB and a whole-region task Jacobian bound. The resulting differential inequality and task triangle budget are explicit in domain.md; no uniform P, residual or Jacobian certificate has been obtained. Contact-free logs do not justify dropping friction/constraint forces.

The original logs are correctly recorded before integration; a suspected timestamp mismatch was refuted. Acceleration replay from q/v/u alone differs by up to0.000249344rad/s² because internal solver warmstart is omitted; supplying the saved acceleration as warmstart removes that discrepancy. This limitation does not affect the fresh independent complete-loop replay.

## Evidence, grade and next action

Evidence levels: independently reproduced binary64 simulations and kinematic diagnostics; exact rational negative controls; nine supporting kernel declarations; hand-derived sufficient coupled contract. Novelty is unassessed, and no physical validation occurred. The source already disclosed the scalar-to-coupled gap and ideal assistance.

Quality rubric: faithfulness4, reproducibility4, discriminatory value4, independent critique4, actionability3 = **19/20,95%**. Subjective confidence is high in the scoped reproducible mechanism and algebra; physical applicability and success probability are unknown.

After all60 initial reviews, spend one30-minute block on a source-bound lead/coupled-residual/total-actuation consumer with the twenty predeclared semantic mutations in next_block_protocol.json. Preserve original task scoring and retain speed/jerk/force tradeoffs. Require valid positive controls and independent rejection checks before promotion. Physical transfer is HOLD pending the named hardware and uniform dynamics premises. No new CLI, hardware command, purchase or service was used.

Primary reference: [MuJoCo computation and actuation](https://mujoco.readthedocs.io/en/stable/computation/index.html). Current documentation informs semantics; pinned runtime/model execution was checked locally. Detailed artifacts and independent critique are in domain.md, inventor.md, critic.md and the saved scripts/JSON/logs.

Final clock supplement: exact reference bounds |qd_dot|≤1/5 and |qd_ddot|≤5/3 imply led-command hold allowance11/30000rad at1kHz. Independent rational replay confirms an interior hold error about0.2473mrad exceeds the old0.2mrad allowance. This bounds held command minus smooth LED reference; the original-reference difference also contains the lead term. Received-before-active history keeps the derivative causal. See domain_hold.md, inventor_hold.md, critic_hold.md and pm_hold_check.json.

Final formal acceptance: seven additional polynomial/conditional mean-value declarations independently compiled and axiom-audited by critic and PM, for16 supporting declarations total. The source piecewise derivative binding and Python rounding remain separate obligations.
