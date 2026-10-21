# R12 led-reference hold allowance

**Accepted, with precise scope:** the original queued analytic reference and an ideal 1kHz hold satisfy a led-command mismatch bound of **11/30000 rad**. This is an interface-error bound, not a physical tracking or Cartesian-output bound.

Let F be the four-box step, h=1/5s, and

q(t)=(1/25)F((t−11/50)/h)−(3/50)F((t−67/100)/h).

The source protocol fixes these events and the 1ms command period. For the unit kernel density g=F', 0≤g≤2/3. On [0,1], g=x³/6. On [1,2], g=(−3x³+12x²−12x+4)/6 and 2/3−g=x(2−x)²/2≥0. Reflection about2 covers [2,4]; outside the support g=0.

For F'', the [0,1] value is x²/2≤1/2. On [1,2], g'=(−3x²+8x−4)/2 and 2/3−g'=(3/2)(x−4/3)². This piece is nonnegative; reflection makes the other half nonpositive. Thus |F''|≤2/3 globally. The kernels join continuously, so these are global bounds, including knots.

The signed velocity contributions lie in [0,2/15] and [−1/5,0], respectively. Therefore |q'|≤1/5rad/s. The second-derivative contributions can have either sign, so use their summed bounds: |q''|≤(1/25+3/50)(2/3)/h²=5/3rad/s².

For the smooth led signal ℓ=q+(1/10s)q',

|ℓ'|≤1/5+(1/10)(5/3)=11/30rad/s.

Its ideal held command u(t)=ℓ(k/1000) on [k/1000,(k+1)/1000) consequently satisfies |u(t)−ℓ(t)|≤11/30000rad by integrating that derivative bound. At update instants the mismatch is zero. This controls the holdError in the identity command=qd+.1qd_dot+holdError. It does **not** give |u−qd|≤11/30000: the lead term remains, with |u−qd|≤.02+11/30000rad as a crude separate bound. Nor does it bound the robot's actual joint position, flange position, torque, or continuous command derivatives.

Causality is preserved for this protocol. Each authoritative packet arrives no later than its execution time; before execution its added position and velocity kernels are zero. Thus evaluating the full two-event analytic formula before an event arrives agrees with evaluating only received history. This relies on the source's receive-time/execution guard and event amplitudes; it does not authorize arbitrary late packets or changed histories.

`critic_hold.py/json` independently binds the source protocol and compares all2001 stored reference samples with exact rational position, velocity and acceleration. Maximum discrepancies are2.5e−17rad,1.2e−16rad/s and1.23e−15rad/s². Those are sample comparisons, not arbitrary-time floating-point bounds. The analytic allowance requires an additional evaluation/clock-error budget to become an implementation certificate.

A meaningful negative control rejects reusing the original .0002rad hold allowance after adding lead. On [1.001,1.002]s the exact led jump is31691721/128000000000rad≈.000247592rad. At the strict interior time1.001999s, the hold mismatch is already greater than .0002rad. The corrected11/30000rad allowance covers both.

Proof status: exact rational arithmetic checks plus the explicit elementary kernel/integral argument above; this supplement is not a Lean-certified ODE or implementation theorem. An initial checker used an incorrect factorization for2/3−g, its assertion failed, and the coefficient identity was corrected to x(2−x)²/2 before acceptance. No source or approved statement changed.

Final card audit: reviewed the completed GO/HOLD card. It preserves the original final-window criterion, original reference/goal scoring, declared new controller, force/transmission distinction, nine conditional proof closures, solver-state limitation and absence of physical transfer. Recommended tightening “No original torque exceedance exists” to a claim about saved rows and model comparison limits, and adding the led hold allowance with the exact interface scope above. Both recommendations were sent to PM; this critic did not edit shared card state.
