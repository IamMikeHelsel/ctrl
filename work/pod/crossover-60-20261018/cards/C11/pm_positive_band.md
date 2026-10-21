# Conditional ODE bridge for the selective band

AI-written hand proof under the ORIGINAL AdaptiveAdmission.Execution, not a general
existence theorem and not yet a single source-bound Lean theorem for the full band.
Assume m_v∈[.029,.030], m_a∈[1.23,1.24], original sensor errors(.001,.01,.05),
0≤D≤.0005, D≤H, pending command−1.21, rate[8,12], target error±.01,
continuous retained state with the source left/right ODE and original age/reading rules.
The source center c=m_x+m_v/4+m_a/32 stays frozen. The old Guard is not assumed.

1. Initial a∈[1.18,1.29]. Since pending effective target lies[−1.22,−1.20],
   the scalar acceleration ODE preserves[−1.3,1.3] by the source's one-sided
   first-contact argument. Thus the pending right derivative for t<D and pending left derivative at D satisfy |a′|≤12(1.22+1.3)=30.24; the right derivative at D is already digital.
2. Original initial v∈[.019,.040]. One-sided mean-value bounds give
   v∈[.01835,.04065] and a≥1.18−30.24D≥1.16488 on[0,D].
3. Tilted coordinates z=(x−c,x−c+v/4,x−c+v/2+a/16) have derivatives
   (v,v+a/4,v+a/2+r(−1.21+d−a)/16). Exact endpoint certificates give
   z0′∈[.01835,.04065], z1′∈[.30957,.36565],
   z2′∈[−1.22165,−.55935]. These bounds use the entire retained enclosure;
   multilinearity and independently checked scalar lemmas justify the endpoint use.
4. Initial coordinate ranges are[−.04725,−.0446875],
   [−.04225,−.0349375], [.0365625,.055375]. Integrating the derivative
   enclosures shows z0,z1 remain negative and increase, while z2 remains positive
   and decreases. Extreme noncrossing bounds are−.044667175,−.034754675,
   and+.035951675 respectively. Thus all |z_i|≤.055375<R=.055525.
5. Original feedback derivative is−8v−6a−r(−1.21+d−a)/2,
   universally in[1.8748,7.1732] on the enclosure for the pending right derivative t<D, hence absolute value≤8.
6. If the source's prefix-budget and delayed-invariant proofs are generalized to
   accept precisely these derived startup-cube and startup-slope premises, their
   remaining age, clipping, residual and first-contact steps apply unchanged.
   Original theorem invocation with a fabricated old Guard is invalid.

Every derivative/mean-value step must retain the original absolute timestamp zero,
left-pending/right-dispatched convention at D, and totalage≤.001. No physical
state is reset. D=0 is included without a pending interval. Startup premises are
not an assumed endpoint cube: steps1–5 derive the entire prefix from the ODE.

This can support a conditional all-time hold argument after the explicit adapter
and remaining ODE bridges are checked. It proves neither existence of the required
execution nor detector reachability. It does not retain the15cm clearance: at mx=.14
and the band's upper corner, c+R=.241775. It is not precision rest or hardware safety.

## Broader coupled polygon

The same argument extends to mv≥.02, .15≤ma≤1.25, 8mv+ma≤1.48.
Its four vertices are in pm_polygon.json. It implies a0∈[.10,1.30],
v0∈[.01,.17625], hence a∈[.08488,1.3], v∈[.00935,.1769].
The first two facets remain negative and increase. The third decreases,
but its lower bound is−.000052825: it may cross zero without approaching−R.
Allstartup magnitudes still≤.055375. Feedback slope lies[.7848,7.2452].
Exact measurement-plane trapezoid area is.08525; original rectangle area.1,
overlaponlyboundary. The UNION has85.25% extra geometric area, not an acceptance
probability, practical utility metric or physical guarantee. This broader polygon
uses the same source center and pending law; independent reviewer checked bounds.
