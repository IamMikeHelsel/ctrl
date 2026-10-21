# R12 domain review: coupled dynamics and total-actuation refinement

AI-assisted domain role; inherited root model, exact identifier unavailable. Root owns timer and PM decision. Original sources, simulator/model cache and recorded traces were read only. No installation, robot connection or hardware action occurred.

## Question, provenance and preserved task

What coupled tracking and total-actuation contract could transfer the scalar checked references to the recorded FR3 simulation or a specified physical Franka? Read frozen README, protocol, run_smoke.py, dependency lock, model-provenance manifest, actual cached FR3 XML, and all16 CSVs under `/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/franka-demo-08`.

The model is Menagerie FR3 at commit62ab00f2bc44f6f20c1c9b7a13f3fb1dd41a4e35; hardware variant is unknown. It has seven hinge joints. The task changes joint1 by+.04rad, with some cases subsequently requesting−.02rad. The measured Cartesian quantity is the world attachment-site position, excluding orientation, tool and gripper. This is a joint-generated flange arc, not a straight-line Cartesian move. Initial state is model home with zero velocity. Retained command history, issue/arrival/execute clocks and1kHz sampling remain part of the contract.

The source evaluates a smooth four-box reference, then holds position commands between1ms updates. Its integration steps are1ms and.5ms, with saved rows every1ms. Reference velocity/acceleration/jerk are not derivatives of the held command. The recorded final criterion is every saved position sample in1.8–2s within.2mm; this is neither all-time tracking nor a settling theorem.

## Transmission and force audit

The XML uses joint actuatorfrcrange limits±87Nm on joints1–4 and±12Nm on joints5–7. Individual actuators have no force clamp; each is attached to one hinge with unit gear. Raw `actuator_force` is not generally the same as delivered `qfrc_actuator`: the latter includes transmission and joint-level clamping. The source CSV's actuator_Nm columns contain the former. This distinction matters even though no recorded row saturates.

The source adds model qfrc_bias as qfrc_applied in assisted mode, outside the joint actuator clamp. MuJoCo's [computation documentation](https://mujoco.readthedocs.io/en/stable/computation/index.html) distinguishes bias, passive, actuator, applied and constraint forces; its [joint force-limit documentation](https://mujoco.readthedocs.io/en/stable/XMLreference.html#body-joint-actuatorfrcrange) specifies the joint-level actuator limit. The numerical audit uses the pinned installed3.16.0 model, rather than assuming every current documentation detail matches that version.

All128 cached model-file hashes match the original manifest. Across all32,016 saved rows, raw actuator force remains inside the joint clamp, so summing raw actuator+bias is valid for these rows. The largest total-force/limit ratio is.3059797704, in the stock hold at.047s, joint2:−26.6202400Nm against87Nm. There is **no recorded torque-limit violation**. The result is an architectural missing total-actuation guarantee, not a claim that these traces exceed their limits.

Four assisted queued-reversal states were independently reconstructed by forward dynamics without integrating another rollout. Raw actuator and model bias match the CSV exactly; clipped generalized actuator force also matches. The full equation M qdd+bias=actuator+applied+passive+constraint closes to2.4e−15Nm using the newly recomputed acceleration. This is forward-dynamics self-consistency, not reproduction of the historical CSV acceleration: the CSV omits qacc_warmstart, and the critic found a separate row where that omitted solver state changes the replayed acceleration. Friction appears in passive/constraint forces even without detected contacts; it must not be discarded as zero merely because the run is contact-free.

## Decisive mechanism: missing reference-velocity forcing

Let qd be the underlying smooth reference, u the held position command, e=q−qd, and Kp,Kv the actual actuator diagonal gains. With delivered actuation equal to raw PD plus clamp discrepancy Δτ, the exact coupled error equation is

M(q)e_ddot+Kv e_dot+Kp e = (bias_assist−bias)+passive+constraint−M(q)qd_ddot−Kv qd_dot+Kp(u−qd)+Δτ.

This keeps the full mass matrix. Bias cancellation alone does not remove the−Kv qd_dot forcing. All source gains have Kv/Kp=.1s. At the worst queued-reversal state, t1.148s, qd_dot1=−.16326785rad/s. The quasi-static diagnostic −.1qd_dot1 predicts+.016326785rad lag; actual e1 is+.0165947129rad, and actual flange tracking error is9.2125981mm. The missing velocity term norm is73.4705325Nm, versus1.5449869Nm for M qd_ddot. These are terms in the error equation, **not actual applied torque or required extra torque headroom**: raw position and damping terms largely cancel. The reconstructed servo/error algebra closes within7.6e−13Nm on selected states.

This is a discriminating explanation of the observed lag, not a uniform tracking theorem. A causal command lead u=qd+.1qd_dot cancels the velocity forcing at update instants while preserving the original reference for scoring. Between updates, residual hold error remains; inertia, friction, model mismatch and clamp discrepancy remain. Root's isolated lead experiment tests this hypothesis against the original qd and retained task/history, not against the led command. The independent critic's separate dynamics-loop replay reproduces root's lead rollout exactly: peak original-reference tracking error.3336468mm, final task-window error.00309712mm, and maximum total-force/limit ratio.2992732. This is about27.6× less peak tracking error, yet still above.2mm during motion. This passes the declared final-window position criterion; it is not a source-task failure. An all-time.2mm tube would be a separate, stronger hypothetical contract. It supports the lag mechanism without establishing the missing all-time tracking contract. The loops share only the original reference evaluator; numerical integration remains.5ms with1ms recorded samples.

## Explicit sufficient transfer contract

The following is a hand-derived sufficient route, not a completed FR3 certificate.

1. Bind the actual variant, payload, frames, actuator transmission, sample/transport policy, firmware/filtering, total-force and force-rate limits. The recorded FR3 model cannot fill unknown physical-arm values.
2. On a forward-invariant configuration/velocity region, bound the complete residual r in the displayed error equation, including model errors, reference derivatives, hold age, passive/constraint forces and clipping. Establish a uniform positive inertia lower bound m. The kernel lemma gives ||acceleration residual||≤||r||/m; four sampled eigenvalues do not establish uniform m.
3. For z=(e,e_dot), use A(q)=[[0,I],[-M⁻¹Kp,-M⁻¹Kv]] and B(q)=[0;M⁻¹]. Establish one common P with pmin I≤P≤pmax I, AᵀP+PA≤−qI and ||PB||≤b throughout that region. If ||r||≤R, Young's inequality gives Vdot≤−q/(2pmax)V+2b²R²/q. Integrating yields an explicit time-dependent state-error budget. This common-P condition is sufficient and may be conservative; no such P or residual bound has been verified here.
4. Establish a task-position Lipschitz bound L over the entire configuration segments joining actual and reference states. Then task error≤L sqrt(V/pmin)+reference-to-authoritative-task error. Final-window samples alone do not supply this all-time bound, and orientation is a separate task component if later added.
5. Check signed total generalized actuation: −T_i−assist_i≤actuator_i≤T_i−assist_i. A simpler sufficient reserve is |actuator_i|≤T_i−B_i with |assist_i|≤B_i. Apply any torque-rate limit to the summed delivered actuation, including assist changes. A reference/command acceptance gate must preserve the retained history and ensure these bounds; clipping without charging its residual invalidates the tracking premise.

The sampled mass matrices have offdiagonal Frobenius norm≈2.355, smallest eigenvalue≈.0741068 and site-Jacobian norm≈.791447. These diagnose coupling and scale; they are not interval certificates over the required region.

## Artifacts and acceptance

- `domain_model.py` / `.json` / `.log`: full saved-row force audit,128 model hashes and four forward-dynamics state reconstructions. Python uses the existing `.tools/franka-sim-python` runtime through uv. No installation or original artifact changes.
- `domain_contract.lean`: nine printed declarations, producer compiled on ctrl's pinned Lean4.33.1, standard axioms only: coupled coercivity bound, exact signed force interval, reserve sufficiency, toy unguarded-assist counterexample, unsaturated error identity, explicit clamp-aware identity, lead cancellation, source gain ratio and task-position triangle budget. The toy10+5>12 example is not a recorded robot sample.
- Independent critic compilation log shows all nine frozen declarations with permitted axioms; final acceptance remains with the PM. Critic separately recomputed all32,016 rows and confirmed the no-exceedance conclusion. Model data and eigenspectra remain floating-point simulator evidence, not kernel certificates.

Reproduce domain numerical audit from ctrl root:
`uv run --no-project --python /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/.tools/franka-sim-python/bin/python python work/pod/crossover-60-20261018/cards/R12/domain_model.py`

Compile from ctrl/lean:
`lake env lean ../work/pod/crossover-60-20261018/cards/R12/domain_contract.lean`

Scoped Python Ruff check/format pass. No fresh full-repository build, formal numerical-integration error certificate, hardware validation or physical settling result is claimed.

Domain recommendation: GO for the causal velocity-lead falsification experiment and coupled residual/total-actuation acceptance contract. HOLD any transfer of the scalar theorem to the existing servo or physical arm until the named uniform dynamics, timing, geometry and hardware assumptions are supplied and checked. Quality18/20=90% (A−): faithfulness4, reproducibility4, discriminatory value4, critique3, actionability3. Subjective confidence97% in the scoped algebra/audit after independent replay; this is not a probability of hardware success.
