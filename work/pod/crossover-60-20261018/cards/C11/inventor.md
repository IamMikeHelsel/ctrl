# C11 inventor — directional startup admission with the original center

AI-written inventor contribution; inherited root model, exact identifier unavailable.
Frozen question: less conservative full-state entry into the C3 tilted hold cube under
actual sensor, pending-command and delay bounds. Read the original C3 report,
AdaptiveAdmission.lean and its DigitalHold.lean input, plus milestone-01/REPORT.txt.
No source file or approved statement was changed.

The source fixes coordinates z=(x-c,x-c+v/4,x-c+v/2+a/16), radius2221/40000,
center c=m_x+m_v/4+m_a/32, pending command-1.21, target error±.01,
rate in[8,12], initial sensor errors(.001,.01,.05), startup D≤.0005 and global
information age≤.001. C3's measured guard is |m_v|≤.02, |m_a|≤1.25.

## Three transfers with explicit failure tests

1. **Robust Chebyshev centering / active constraints.** For any fixed measurement and
uncertainty set, each facet gives an allowed interval for c; a robust center must lie in
the intersection. Optimizing that intersection can remove conservatism of the preselected
center, but it changes the command and translated physical tube and must be declared.
The root/domain work owns that alternative. A crucial negative: universal containment
in a polyhedron is exactly equivalent to separate support bounds for every facet.
The facet maxima need not occur at one common physical state. Their incompatibility
alone does not justify weakening any bound. Falsifier: a proposed smaller bound excludes
a state attaining a single facet merely because that state does not attain all others.

2. **Monotone reachability and directional abstract interpretation.** Preserve the actual
pending dynamics, rather than enclosing every coordinate's drift by a symmetric magnitude.
A signed facet can move inward during the whole startup even if the enclosing coordinate
box expands. The exact positive reading band below keeps the original center, feedback,
sensors, pending target and startup horizon. It uses the ODE's directional information,
not an unproved correlation between independent sensor errors. Falsifier: reverse the
pending command, or retain only time-zero containment; the asserted inward signs fail.
The domain supplies a separate initially admissible boundary state that immediately exits,
showing why whole-prefix dynamics are necessary.

3. **Unexpected transfer: real-time scheduling as spatial budget reservation.** An admission
certificate can attach a latest permissible dispatch to a measurement: reserve both facet
margin and the remaining information-age budget before accepting it. These are distinct
resources. An inward-moving facet may gain geometric margin while the reading becomes
older; neither margin permits resetting its timestamp. A future packet-dependent guard
could intersect its directional entry certificate with a scheduler-provided upper bound
on D. This preserves actual state/history and uses no preview. Falsifier: restarting the
1ms age clock at dispatch, or extending D beyond the source's .5ms startup contract solely
because a signed facet remains inward. This review keeps the original D and global clock;
it does not claim a longer delay theorem.

## New positive-width band and exact arithmetic

Take measured m_v in[.029,.030] m/s and m_a in[1.23,1.24] m/s², with arbitrary m_x.
Every reading in this band violates the old speed guard. Nevertheless, retain the original
center policy and every independent source sensor error. The exact initial facet ranges are

| Facet | Lower | Upper |
|---|---:|---:|
| z0 | -.04725 | -.0446875 |
| z1 | -.04225 | -.0349375 |
| z2 | .0365625 | .055375 |

All lie inside R=.055525. The pending target including error lies in[-1.22,-1.2].
The same scalar barrier argument as the source yields |a|≤1.3; hence |a'|≤30.24.
Integrating for D≤.0005 gives a≥1.18-30.24D≥1.16488 and
v in[.019-1.3D,.040+1.3D]⊆[.01835,.04065]. These are derived envelope claims,
not arbitrary initial-box assumptions. Rebinding this ODE barrier to the new measured
band is still a required formal bridge.

Using a'=r(-1.21+d-a), exact universal algebra gives

| Facet derivative | Lower | Upper |
|---|---:|---:|
| z0' | .01835 | .04065 |
| z1' | .30957 | .36565 |
| z2' | -1.22165 | -.55935 |

For example z2'=v-.6-(r-8)(a+1.2)/16+r(d-.01)/16≤v-.6. This signed cancellation
is stronger than separately adding |v|,|a|/2 and |a'|/16. Opposite-side integral
bounds ensure z0,z1 remain negative and z2 remains positive for the whole startup.
Thus all three absolute coordinates decrease, and their maximal startup magnitude
is at most.055375, leaving margin.00015. The actual pending feedback derivative lies
in[1.8748,7.1732], retaining the source's bound8 for the later age calculation.

A symmetric coordinate-drift inflation gives .056665325 for z2 and rejects the same
band. That is a genuine representation/dynamics improvement. It does not rely on the
false assertion that independent facet support bounds must be jointly attainable.
The guard is nonempty with positive reading width and certifies every state in each
reading's sensor box. It does not prove a detector necessarily reaches or observes it.

## Artifacts, negative controls and acceptance boundary

`inventor_pending.py/json` independently enumerates the exact initial sensor corners and
multi-affine derivative extrema, checks the opposite-side signs, source feedback slope,
new margin and old-box rejection. It also shows reversing the pending command destroys
the z2 inward certificate. Enumeration is a finite algebra check; it is not an ODE solver
or a complete infinite-execution certificate.

`inventor_facets.lean` proves seven scalar universal statements: initial sensor-box facet
ranges, third-facet upper/lower drift, positivity of the first two drifts, no sign crossing
under the integrated envelopes, the exact margin, and the feedback slope range. It compiled
with only propext, Classical.choice, Quot.sound. Frozen SHA256:
653d8ccd6806ecd3c1cdcefb1a2781a242fa1979e265864715012cb9bc57cc3b.
The unused nonnegative-time hypothesis warning on the simple arithmetic barrier is benign.

GO: bind the new band to the generalized admission wrapper completed in the supplement
below, proving its same-source ODE/integration bridge under the unchanged global clock. The existing
AdaptiveAdmission.delayed_sampled_hold still hard-requires the old Guard; it cannot be
invoked directly on this band. Full all-time delayed-hold certification, detector liveness
and physical robot validation remain unclaimed. The next experiment should also replay
the domain's initially admissible/outward boundary negative and the source's stale-reading
negative, so an endpoint-only or clock-reset adapter fails explicitly.

Quality18/20 (faithfulness4,reproducibility4,discrimination4,critique3,actionability3).
Subjective confidence98% in exact algebra; the unintegrated ODE bridge is a named limitation,
not a physical success probability.

Nearby negative control: merely raising the old independent speed cap to .03 while retaining
m_a=1.25 gives initial worst z2=.0556875, exceeding R by .0001625. The source's original
widening counterexample remains valid. The new band lowers m_a to at most1.24 and proves
its directional whole-prefix behavior; it is not that rejected blanket guard widening.


## Completed actual-source adapter supplement

`inventor_adapter.lean` imports the original AdaptiveAdmission module and generalizes only
its `prefix_budget` and `delayed_invariant` proof bodies. The two replacements are explicit:
startup cube containment on [0,D], and actual pending feedback-slope bound8 on [0,D).
Original Guard/Admitted is not assumed. The original Execution, fixed center policy,
right/left dynamics, global information age, clipping, radius, rate/error contract and
startup limit remain bound to the actual source definitions. Prefix cube hypotheses are
still discharged by the original first-contact argument; no ongoing cube is assumed.

Both declarations compiled under the source's pinned Lean4.35 with only propext,
Classical.choice, Quot.sound. Frozen SHA256:
519e00837db0cc2de811ef6f41dc0accce352c55bb3582e24341521ced43b60f.
`inventor_adapter_replay.py/json` verifies the imported cache's Lean source copies against
the original two source files, records the executable/path/hash and exit status, and
writes only this campaign's artifacts. This uses the existing accepted cache as its base;
it does not claim a fresh rebuild of the original closure. The warnings mark retained
explicit delay premises unused in this more general conditional proof.

The domain separately compiled an actual-Execution acceleration barrier from the new
initial physical bound. The remaining positive-band bridge is integration plus directional
whole-prefix facet bounds and pending slope binding. Until it is compiled and independently
checked, this is a source-bound conditional all-time adapter, not a completed new-band
all-time hold theorem. Independent critic replay is requested separately.
