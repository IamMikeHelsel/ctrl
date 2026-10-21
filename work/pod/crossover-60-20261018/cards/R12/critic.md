# R12 independent critique

A coupled, clamp-aware contract is necessary, but the recorded FR3 traces do not show a total-force limit violation. A causal velocity lead is a promising new experiment: it greatly improves this simulation's tracking while still not establishing a hypothetical uniform 0.2mm tube and increasing sampled speed and jerk. Neither result transfers the scalar theorem to a physical Franka arm.

## Original evidence and force semantics

The original README already discloses ideal generalized bias assistance, the uncertain hardware variant, and the scalar-to-coupled-model gap. The source script hash matches its recorded summary. All 128 pinned model files match their manifest; the existing runtime is MuJoCo 3.16.0. No package installation, hardware access, or original-file modification occurred.

`critic_trace.py` independently reconstructs all 32,016 saved rows with `mj_forward`. Runtime inspection establishes seven direct joint transmissions, unit gears, matching joint/DOF/actuator order, and joint actuator-force ranges [87,87,87,87,12,12,12] Nm. The clamp is attached to each joint; raw actuator output need not equal delivered generalized force when saturated. In these original traces it does: actuator-force, generalized-force, bias, and flange-position reconstruction errors are exactly zero.

Every original row's delivered actuator plus bias force remains below the model limits. The worst ratio is 0.3059797704: stock hold joint2, -26.620240Nm against 87Nm at t=.047s. The assisted queued .5ms trace peaks at ratio .2991181581. Thus an original-trace exceedance claim is refuted. These are sampled model-limit checks, not physical motor-limit certification or continuous-time bounds.

The structural bypass is independently demonstrated with a changed reference: source home, joint2 command offset -.5rad. Raw actuator output is -2250Nm, delivered output clamps to -87Nm, bias is -25.999663Nm, and their total is -112.999663Nm. This is explicitly not an original task or recorded failure. A gear-two mutation separately gives raw force4.5 and generalized force9, rejecting componentwise addition without transmission validation.

The suspected row-timing mismatch does not apply. Source logging occurs after two forward calls and before stepping; all logged force and position fields bind to that state. Acceleration reconstruction differs by at most .0002493442rad/s² when internal solver warmstart is omitted. At the worst row, setting warmstart to the saved acceleration removes the discrepancy exactly. The source CSV does not record full solver state. `critic_solver_state.json` and `critic_initial_replay_note.md` retain this limitation and the initial checker timestep correction.

## Tracking, coupling, and interface checks

The queued assisted fine-step run has 9.212598124mm maximum reference-tracking error despite passing its final-window task test with .112451681mm error. Final proximity does not imply a transient tube. The task scores world-frame attachment-site position only; it does not constrain orientation, payload, speed, acceleration, or physical settling.

Exact negative controls show why scalar composition is insufficient: an SPD two-by-two inertia matrix with off-diagonal coupling produces acceleration on an uncommanded coordinate; isolated stable scalar loops can also have an unstable interconnection. Endpoint-only Jacobian norms cannot certify a whole-segment Lipschitz bound, and values at sample times cannot certify a continuous tube. These are countermodels to missing premises, not alternative FR3 dynamics.

`critic_kinematics.py` independently checks all sixteen root peak-state Jacobian diagnostics using centered differences. Their local norms and linearization remainders agree. A transfer theorem still needs a uniform bound over the admitted state/reference region, with units converting radians to meters and explicit residual, contact/friction, actuation, and reference-interface budgets.

The original emitted position command is a 1kHz staircase. The continuous reference's analytic jerk is not its ordinary command jerk. The inventor's exact queued-reference allowance is 1/5000rad for ideal zero-order hold, not 0.2mm of Cartesian error. It still requires an independently justified coupled response and geometric bound.

`critic_energy.py` independently reproduces all sixteen mechanical-work and squared-torque quadratures. Assisted hold has exactly zero stored velocity and mechanical work while maintaining approximately26Nm of bias and over2000Nm²s of squared-force duty. Small signed work therefore cannot replace force or thermal budgets; no electrical-energy or temperature measurements exist here.

## New causal lead experiment

The domain algebra exposes reference-velocity forcing from the source position servo's velocity damping; all source Kv/Kp ratios equal .1s. A command qd+.1qd_dot can cancel that term, leaving inertia, friction, hold error, model residuals and saturation to be bounded.

`critic_lead.py` implements a fresh dynamics loop with the original ReferenceHistory as its only shared controller code. It reproduces the producer's complete .5ms lead array bit-for-bit, scoring against the original reference and original goal. Peak tracking decreases from9.212598mm to .333646792mm and final-window error to .003097120mm. However, peak goal error increases to31.954445mm, sampled speed to .201753889rad/s, and sampled jerk to147.989117rad/s³. Total-force ratio remains .299273186. The .333647mm transient peak exceeds a hypothetical uniform .2mm tube; the source acceptance test is final-window-only and passes. This is a declared new controller and numerical experiment, not a repaired claim about the original controller.

The dependency negative also reproduces bit-for-bit in a separate fresh stock-mode loop (`critic_lead_stock.py/json`). Removing ideal bias assistance while retaining the .1s lead yields6.053464068mm final-window error, failing the actual source .2mm final criterion. Peak tracking is also6.053464068mm. This confirms that velocity lead alone does not replace the ideal bias assistance; no physical Franka failure is inferred.

## Formal acceptance and decision

The nine declarations in domain_contract.lean were independently compiled and inspected. They establish conditional coupled acceleration, signed force headroom, conservative reserve, clamp-aware error identities, velocity-lead cancellation, the gain ratio and triangle-inequality task-budget composition. They do not establish a closed-loop tracking tube, a uniform inertia/Jacobian bound, or a refinement of the MuJoCo/runtime/hardware implementation. The clamp-aware identity correctly includes delivered-minus-raw actuator residual; omitting it would invalidate saturated extensions.

The six critic scripts pass scoped Ruff and formatting checks. `critic_next_gate.json` contains twenty proposed semantic mutations and positive controls; that continuation block has not run. No repository-wide integration checks are claimed.

**GO** for an explicit coupled residual and total-actuation admission contract, with the causal lead as a discriminating controller candidate. Require unchanged task scoring and report all speed/jerk/force tradeoffs. **HOLD** for a 0.2mm continuous task tube or hardware transfer pending uniform dynamics/geometry bounds, exact hardware specification, and runtime refinement. **NO-GO** for treating final-window success, low mechanical work, or the retained actuator clamp alone as the missing certificate.

Evidence: exact rational negative controls, binary64 reconstruction and simulation, and conditional Lean algebra. Quality:4/5 for this initial review. Subjective confidence is high in the reproduced diagnostics and scoped algebra; physical transfer remains unassessed.
