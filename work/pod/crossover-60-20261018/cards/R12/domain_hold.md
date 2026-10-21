# R12 supplement: conservative1kHz hold budget for the causal velocity lead

This is a final-review supplement, not a30-minute extension. Root owns campaign timing. Original reference/history, model and results remain unchanged.

For the queued source, h=1/5s, first execution is11/50s=.22s, and reversal execution is67/100s=.67s. The retained increments are+1/25rad=.04rad and−3/50rad=−.06rad. Let F be the integrated four-unit-box kernel, exactly as the analytic curve represented by source `box_step`. Then joint1's reference offset is

qd(t)=(1/25)F(5(t−11/50))−(3/50)F(5(t−67/100)).

The home coordinate adds a constant and does not affect these bounds. All other joint references remain constant.

On0≤z≤1, F'(z)=z³/6 and F''(z)=z²/2. On1≤z≤2, F'(z)=(−3z³+12z²−12z+4)/6 and F''(z)=(−3z²+8z−4)/2. The density F' is reflected across z=2 on[2,4], while F'' changes sign under reflection; both are zero outside[0,4]. Direct polynomial bounds give0≤F'≤2/3 and |F''|≤2/3 globally. Endpoint values match, so these are the actual continuous derivatives, including the knots. This derivative identification follows by differentiating the source's piecewise quartic formula; the Lean supplement separately checks the four polynomial envelopes rather than claiming the Python evaluator itself is kernel bound.

Writing a and b for the two shifted density values,

qd_dot=(1/5)a−(3/10)b, with0≤a,b≤2/3.

Consequently −1/5≤qd_dot≤2/15, and |qd_dot|≤1/5rad/s=.2rad/s. The opposite signs matter: a triangle bound would unnecessarily give1/3rad/s. No assumption about nonoverlap is needed. The speed bound is attained at t107/100s=1.07s: the first event is already complete (normalized time17/4), while the negative event has normalized time2 and density2/3.

The acceleration is qd_ddot=F''(z1)−(3/2)F''(z2), so

|qd_ddot|≤2/3+(3/2)(2/3)=5/3rad/s².

This second bound deliberately ignores cancellations and is conservative. The supplied event separation is retained; the envelope holds for this separation without requiring a search for the exact maximum.

For the led command g(t)=qd(t)+(1/10)qd_dot(t),

|g_dot(t)|≤1/5+(1/10)(5/3)=11/30rad/s.

At an update time tn, hold g(tn) until the next update. If0≤t−tn≤1/1000s, the mean-value/integral bound gives

|g(t)−g(tn)|≤(11/30)(1/1000)=11/30000rad≈.0003666667rad=.3666667mrad.

The previous unled bound was(1/5)(1/1000)=1/5000rad=.2mrad. Reusing that old budget for the lead is unsupported; the conservative new budget is11/6 times as large. This is a command-coordinate error budget, not a task-space.2mm budget and not a measured tracking error.

Assumptions: the1kHz hold uses the same causal analytic qd and its derivative, keeps the actual retained command history, and has no additional age beyond1ms. A maximum additional delay d changes the envelope to(11/30)(.001+d). A sample evaluation error bounded by eta adds eta to the command error. The floating-point source evaluation has not been given a rigorous eta certificate here. Command clipping or other filtering introduces further discrepancy and must remain in the clamp/hold residual contract. Physical sensor noise does not enter this planner-only reference formula, but may enter the separate tracking model.

`domain_hold.lean` checks the four polynomial envelopes, the queued velocity and acceleration combinations, and a mean-value hold theorem with explicit HasDerivAt and derivative-envelope hypotheses. That theorem proves11/30000 for any functions satisfying those hypotheses; the complete source-function derivative binding and Python floating-point evaluation remain separate obligations. All seven printed declarations producer-compile with permitted axioms; independent critic replay is requested on the frozen file. A failed preliminary absolute-value lemma invocation is preserved separately and not accepted. Compile from ctrl/lean with `lake env lean ../work/pod/crossover-60-20261018/cards/R12/domain_hold.lean`.
