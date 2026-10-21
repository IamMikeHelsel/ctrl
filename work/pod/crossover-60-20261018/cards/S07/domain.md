# S07 domain — exact active-mode geometry

AI-written; inherited root model, exact runtime identifier unavailable. Read original SaturationBoundary, TravelSafety, SaturatedLag, TravelGeometry, Generated/TravelQuarterLower, StepScaledRobustness and relevant README passages. Original files/toolchain pins are unchanged. Isolated proofs use ctrl's existing pinned Lean environment, not a fresh rebuild of every notebook dependency.

The two source claims concern different models. The rounded sampled-PD local budget in SaturationBoundary proves clipping inactive. TravelSafety instead defines the normalized actuator-lag plant x'=v,v'=a,a'=−a+u with sampled request c·z=−x−3v−2a and held actual drive clamp(c·z,−1,1)+w. The command and disturbance stay fixed during each interval; |w|≤.01, interval≤.2, positive minimum interval for covering all real times. The disturbance enters AFTER the clamp; total drive can reach1.01. This is not a torque-calibrated robot model or arbitrary time-varying within-hold disturbance theorem.

For each segment alpha is computed from its INITIAL request and then held. It is not reselected from the evolving state. Source TravelSafety already proves all-time |x|≤2 for V=zᵀPz≤12, with genuinely active witness(0,0,1): V278/25,request−2,clamp−1. The question's phrase 'include active clipping' cannot mean every point or every future instant clips: the origin is inside the set and inactive.

## Sharp geometry and a meaningful expansion limit

The exact source matrix is

    P=[[38/5,257/25,5],[257/25,1319/50,769/50],[5,769/50,278/25]].

Exact rational elimination gives

    κ=cᵀP⁻¹c=4133475/11131832,
    σ=(P⁻¹)00=3550075/11131832.

Hence input²≤κV and x²≤σV, with equality on the corresponding P⁻¹ covector directions. The residual matrices κP−ccᵀ and σP−e0e0ᵀ have explicit rank-two rational LDL decompositions. `domain_geometry.lean` checks their sum-of-two-squares identities and inequalities against the scalar expansion of the literal P. The equality/maximizer characterization is a hand Cauchy–Schwarz argument, not a separately formalized optimization theorem.

AtV≤12, maximum|input|=sqrt(12400425/2782958)≈2.110886872, so actual minimum sector ratio is≈.47373453 rather than the source's conservative1/4. Strictly active halfspaces intersect V≤R exactly whenR>11131832/4133475≈2.693. At equality the set only touches clamp boundaries; no strict clipping occurs.

Exact request2 witness:

    z=(15134,−50732,−96808)/165339,
    V=44527328/4133475<11<12.

This is useful for a smaller E11 core; the source's older witness V11.12 would not belong to that core.

Preserving the SAME ±2 travel tube under unrestricted dilation of this same ellipsoid requires

    R≤Rtravel=44527328/3550075≈12.54264431.

The quarter-sector condition alone permitsR≤178109312/4133475≈43.09, so travel is the active geometric restriction. AtRtravel both |x|≤2 and |input|≤4 are kernel checked, as is the original disturbance budget at that radius. This is a geometric/budget extension, not by itself a newly assembled all-time execution theorem.

An exact negative shows why unrestricted further inflation fails: E13 contains

    z=(201/100,−9400167/7100150,3292179/3550075),
    V=56217143079/4437593750<13,

but x=2.01 already violates travel at timezero. `domain_expansion_negative.json` records it. Alternative-shaped sets can still extend beyond E_Rtravel; this counterexample concerns the whole ellipsoid E13.

## Budget does not secretly remove active states

The unchanged elapsed-time budget with eta5/451,C13,H1/5,W1/100 is EXACTLY

    R≥662519/62500=10.600304.

For every suchR, the simple point(0,0,3/4) has V1251/200=6.255<R and request−3/2. Therefore the budget cannot force clipping inactive in this model. The interval[10.600304,12.54264431] is nonempty and includes the original12. `domain_budget.lean` checks the floor equivalence, strict active witness inequality and interval arithmetic. A wrapper using original contraction/disturbance/source dynamics is a separate obligation owned by root.

For geometric perspective only: a linear ellipsoid-to-ball transform shows the strictly active subset occupies fraction1−3b/2+b³/2, b=1/sqrt(12κ), approximately34.2557% of ellipsoid volume. This is a hand volume calculation, not a stochastic guarantee or fraction of time a trajectory clips.

## Cross-check of root's different-shape proposal

For g=(1,−1,1), c·g=0 and the held plant transports g to exp(−t)g without changing the initial clamp request. Root proposes E11+[-1/8,1/8]g. Exact domain arithmetic confirms V((17/10)g)=54621/5000<11, while its lift(73/40)g hasV1007181/80000≈12.5897625, beyondRtravel. The core has the genuine request2 witness above. This is a meaningful way around the same-ellipsoid travel obstruction. Source execution assembly, invariance of the decomposition, and all-time bound must still be proved; these scalar checks do not silently supply them.

## Evidence and next action

`domain_geometry.py/json` computes exact inversion and LDL residuals and generates seven scalar Lean declarations; `domain_budget.lean` adds three. Initial failed logs are preserved. Critic independently reconstructed geometry and mutation tests. Numerical square roots/volume percentages are illustrative; rational coefficients, inequalities and witnesses carry the evidence. No solver-only certificate, physical acceptance, new saturation-control novelty, or full notebook rebuild is claimed.

GO for the bounded wrapper/capsule test; NO-GO for advertising the local rounded-PD budget as an active-clipping basin or enlarging the full P-ellipsoid beyondRtravel while promising identical travel. Quality18/20(90%); subjective confidence high in source-bound algebra and geometry, with execution composition remaining a distinct obligation.

Final producer checks: geometry7 and budget3 compile with only propext/Classical.choice/Quot.sound; failed initial logs are retained. A separate-directory generator replay produces byte-identical geometry Lean. Scoped Ruff and formatting pass. Domain independently compiled critic_semantics.lean4, with allowed axioms, and inspected its literal-source bindings: request evolution, missing off-diagonal energy, pre/post-clamp distinction, and an explicitly out-of-scope five-unit hold. No repository-wide integration check was substituted for this scoped evidence; root owns final campaign checks.

Capsule follow-up materially changes the recommendation: K(11,1/8) is not nested withE12 and is2.59% smaller in volume. The repaired K+=E12+[-1/25,1/25]g is a strict superset, grows volume by about3.37%, retains the same travel margin, and contains an explicitly clipped point outsideE12. See domain_capsule.md for exact support, volume and witness derivations. Four additional domain capsule lemmas pass, bringing the domain total to14; the convex-body volume formula remains hand-derived and the actual-source dynamics wrapper remains root-owned.
