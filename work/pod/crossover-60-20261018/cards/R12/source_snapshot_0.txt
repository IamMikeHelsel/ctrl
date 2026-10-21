FRANKA DEMO PREPARATION — 17 October 2026 local time

Status: executed simulation infrastructure, with an explicit model gap.
Mike selected Franka robots for the eventual hardware demonstration. The exact
variant is unknown. This rehearsal uses the Menagerie FR3 model. It does not
assume that the available arm is an FR3 or that Panda software is interchangeable.

What ran
Four tasks: hold; one small move; a goal reversal during that move; and a delayed
reversal with a retained 60 ms execution commitment. The first move is 0.04 rad on
joint 1. The reversal requests -0.02 rad. The other joint goals remain at model home.
The task geometry is the model's world-frame attachment-site position, called
flange position here. It excludes orientation, a tool, and a gripper. This is a joint
motion that traces a flange arc, not a straight Cartesian 20 mm task.

Two servo configurations use the original model's position actuators and gains.
The first uses those actuators alone. The second adds the model's gravity and
Coriolis bias as an ideal generalized-force assist at each integration step.
This assist is not a reproduction of Franka firmware or its impedance controller.
The second configuration does not compensate the model's friction.
Its generalized-force assist is outside the position actuator's force clamp.
Keeping that clamp unchanged does not bound the total applied joint torque.

Both run at 1 ms and 0.5 ms integration steps. Commands arrive on the same simulated
1 kHz clock in both. Thus there are 16 runs and 32,016 saved rows. These are repeated
integration checks, not 16 independent real-world trials. The reference is our
four-box history, evaluated numerically in Python. No real-time claim is made
about the Python implementation. No robot connection exists in this program.
Reported analytic reference derivatives describe the underlying continuous
curve. They are not derivatives of the emitted position command, which is held
between 1 kHz command updates.

The protocol and implementation were hashed before physical integration. All
128 downloaded FR3/Panda model files have pinned hashes. Only FR3 was executed.
The model commit is 62ab00f2bc44f6f20c1c9b7a13f3fb1dd41a4e35. The exact dependency
versions are in requirements.lock.txt. MuJoCo is 3.16.0, Python is 3.12.15.

What the checks establish
All 16 integrations completed with finite states, no MuJoCo warning, and no
detected contact. Command samples match bit-for-bit across the two time steps.
The largest flange-position difference between time steps is 0.069951 mm over
the full trace. This is a refinement diagnostic, not a rigorous error bound.

The separate audit compares the four-box step against scipy.stats.irwinhall(4),
checks the retained prefix, rejects four invalid packet cases, and recomputes
the final task score from every CSV. It is a coordinator check, not an independent
plant replay. The maximum primitive discrepancy is 2.22e-16.

All eight stock-actuator runs fail the illustrative 0.2 mm final-position band.
Their final flange error is about 6.053 mm; even the hold sags under gravity.
All eight ideal-bias-assist runs meet the sampled final-position band from 1.8 s
through 2 s. At the finer integration step, maximum final-window errors are:
hold 0 mm, single move 0.0045 mm, reversal 0.0579 mm, queued reversal 0.1125 mm.
No final speed/acceleration test or physical settling theorem is claimed.

The queued reversal with ideal bias assist has peak reference-tracking error
about 9.213 mm during motion. A small final error does not repair this earlier
deviation. The present scalar Lean bound cannot be transferred to this servo.
The stock model failure is not a claim that a real Franka arm sags by 6 mm.

Why this matters
We now have reproducible seven-joint traces, flange measurements, causal command
history, a model pin, and a short render. They expose the model/controller gap
before hardware. They do not show superiority over Ruckig, a learned policy,
Franka's internal controller, or an industrial planner. No such comparison is
hidden in this smoke test. The separate moving-goal08 experiment uses the
previous scalar plant and the competitive native baselines.

Reproduce from the working research root
1. uv venv .tools/franka-sim-python --python 3.12
2. uv pip install --python .tools/franka-sim-python/bin/python -r research/pods/2026-10-17/robot-motion/franka-demo-08/requirements.lock.txt
3. .tools/franka-sim-python/bin/python research/pods/2026-10-17/robot-motion/franka-demo-08/prepare_model.py .tools/mujoco-menagerie --manifest research/pods/2026-10-17/robot-motion/franka-demo-08/model-provenance.json
4. .tools/franka-sim-python/bin/python research/pods/2026-10-17/robot-motion/franka-demo-08/run_smoke.py --model-root .tools/mujoco-menagerie
5. .tools/franka-sim-python/bin/python research/pods/2026-10-17/robot-motion/franka-demo-08/audit_smoke.py
6. .tools/franka-sim-python/bin/python research/pods/2026-10-17/robot-motion/franka-demo-08/render_smoke.py --model-root .tools/mujoco-menagerie --video

Use a copy or '--output NEW_DIRECTORY' for another run so the recorded evidence
stays intact. The audit targets the recorded results directory. Rendering uses
saved states; it does not rerun physics. The 6 s video plays 2 s of simulation at
one-third speed. No installed runtime or model cache is included in the notebook;
the dependency lock and pinned model fetcher reconstruct them. Docker was not
needed for this local macOS simulation. Hardware has different host requirements.

Sources and next implementation choices: hardware-plan.txt and prior-work.txt.
Sources retain their own licenses. Menagerie model files use Apache-2.0.
The future robot test still needs the exact arm, software, payload, frames,
controller settings, and a measured execution interface.
