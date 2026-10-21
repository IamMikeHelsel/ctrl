# R07 independent paired-damping audit

The proposed policy is correct for the declared ideal model. This is an analytic audit with exact rational constants; the ODE solution and all-time comparison are hand-derived, not a new kernel theorem.

Assume M=diag(1,2), no other forces, exact current velocity, initial q2=−q1, v2=−v1 and v1≥0. After a coast delay δ≥0, command

a1=−min(a,k*v1), a2=−a1, with a=1/10 and k=5/2.

Implement with τ1=a1, τ2=2*a2, so |τ1|≤1/10 and |τ2|≤1/5. The task acceleration a1+a2 is identically zero; the initial task-position and task-velocity conditions therefore preserve q1+q2=0. Without those two initial conditions, paired accelerations alone do not establish a zero task error.

Let v0 be the speed at braking admission. Set v*=a/k=1/25=.04. If v0≥v*, the saturation phase lasts

t1=(v0−v*)/a.

During it, v(s)=v0−a*s and the displacement is (v0²−v*²)/(2a). Thereafter v(s)=v* exp(−k(s−t1)); the remaining infinite-horizon displacement is v*/k=a/k². Thus the total asymptotic braking displacement is

D(v0)=v0²/(2a)+a/(2k²)=5*v0²+1/125=5*v0²+.008.

If0≤v0≤v*, there is only exponential decay and D(v0)=v0/k≤2/125=.016. The two formulas agree at v*. This policy has no zero-crossing event and v(s)>0 at every finite braking time when v0>0. Its limit is rest, not finite-time exact rest.

Both D(v0) and the coast displacement δ*v0 are nondecreasing for v0≥0. Consequently, for q10≤9/50, v0≤1/5 and δ≤1/20,

sup q1 ≤9/50+(1/20)(1/5)+D(1/5)
        =9/50+1/100+26/125
        =199/500=.398<2/5.

Hence sup(q1−q2)≤199/250=.796<.8. For positive speed the supremum is approached asymptotically, with every finite position below it. Lower joint safety additionally requires the initial joint box: q10≥−1 and q20=−q10. Since q1 is nondecreasing and q2=−q1, these entry bounds together with the new upper bound imply both joints remain in[-1,1]. The upper condition q10≤.18 alone would not imply lower-joint safety.

## Explicit positive residual tolerances

For a requested velocity tolerance ε>0, this exact model gives a finite tolerance deadline even though exact rest is asymptotic. In the saturated-entry case and ε<v*, speed is at most ε after

braking time t1 + (1/k) log(v*/ε).

At that time the remaining displacement is at most ε/k and acceleration magnitude is at most k*ε. Uniformly over v0≤.2 and δ≤.05, t1≤1.6, so one may use issue-relative time1.65+(2/5)log((1/25)/ε) when ε<1/25. These are explicit model-dependent residual bounds, not a reuse of any physical robot or prior scalar benchmark tolerance.

The margin.002 in q1 is ideal-model margin, not a proven sensor/model robustness budget. Unknown inertia, velocity noise, delay during the feedback phase, actuator mismatch and force disturbances require new bounds. With changed mass, commanding paired torques based on the old exact inertia generally breaks task cancellation; the prior mass-mismatch witness remains valid.
