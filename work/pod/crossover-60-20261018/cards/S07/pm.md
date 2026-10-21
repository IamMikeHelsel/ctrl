# S07 program-manager research

AI-written. Four concurrent roles, all inherited root model; exact runtime identity unavailable. No model-family diversity or Spark inference is claimed. Root is PM. Setup/context recovery excluded from state.json elapsed accounting.

Original question: Can a robust invariant include genuinely active clipping throughout a region without relying on a budget that secretly forces clipping inactive?

The existing TravelSafety source already answers yes for region-wide invariance with an active subset. It does not say every point clips, nor that clipping persists along every trajectory. The separate SaturationBoundary local budget excludes clipping; do not transfer that limitation or its theorem to the different travel model.

Source model: x'=v,v'=a,a'=-a+u; sample-and-hold u=clamp1(-x0-3v0-2a0)+w, held |w|≤.01, 0<hmin≤h_n≤.2. Source P and V are unchanged. Disturbance is after saturation. Current state request is not re-evaluated midhold. Existing E12 is invariant for all real t≥0 and guarantees |x|≤2.

Three transfers tested:

1. Convex dual geometry: intersect ellipsoids with the active halfspaces. Exact support c'P^-1c=4133475/11131832; active subset begins above radius11131832/4133475. Source robust radius floor10.600304 is above this threshold, not a hidden inactive restriction. Sharp position support gives maximum same-P corridor-compatible radius44527328/3550075≈12.542644. Full E13 already violates travel at timezero.
2. Hybrid/complementarity semantics: distinguish frozen sampled command from the current unsaturated request. Inventor's entire rational box is initially clipped but current request is inactive after.1; actual held command stays clipped. Re-selecting a sector gain midhold changes the system. Affine/LDL geometry and exact negative controls test this mapping.
3. Unexpected symmetry/quotient transfer: define p=x+v,b=v+a. They obey p'=b,b'=u, and request=-p-2b. Hidden g=(1,-1,1) leaves the complete command trace unchanged while its state offset decays as δexp(-t)g. This is a model symmetry with a physical-position budget, not equivalence of physical travel. The same w/h sequence can be coupled to an auxiliary core for every actual sequence.

The first shape E11+[-1/8,1/8]g is valid in hand derivation with independently kernel-proved E11 core, but NOT a superset of E12; volume is2.59% smaller. This criticism produced the better shape K=E12+[-1/25,1/25]g. Sharp source-bound position≤49/25 leaves1/25 reserve. K strictly contains E12, remains invariant under exactly the original source execution, and guarantees |x|≤2 for all t≥0. Root pm_source_complete.lean proves held symmetry, contraction of hidden offset, sample and real-time recurrence, source-bound position safety, containment, and explicit strictness. Copied critic sharp-position SOS is attributed and counted only once. Initial namespace failures/sorryAx logs are retained and rejected; only final successful exact bytes are accepted.

Geometry alone gives volume(K)/volume(E12)=1+(3/50)sqrt(63/200)≈1.033674916. This volume formula is hand-derived with exact scalar checks, not a kernel volume theorem. K includes input-active new points: core(29/20,-27/20,37/20) has energy237409/20000<12; shifting g/25 gives(149/100,-139/100,189/100), energy6166449/500000>12, request-11/10, clamp-1. A separate zero-request example lies beyond the largest same-P dilation. Do not conflate those witnesses.

Root's exact membership experiment minimizes V(z-δg) on δ∈[-1/25,1/25]. δ*=clip((g'Pz)/(g'Pg)), g'Pg=189/50. Six exact fixtures include newly admitted clipped and beyond-dilation states, and rejected excessive-travel/too-wide caps. Exact slope signs certify constrained minimum; no numerical solver acceptance. A production certificate consumer and full formal membership decision procedure remain future work.

Independent negatives: wrong lagrate, different copied disturbance, different sampling schedule, moving disturbance before clamp, switching disturbance within a hold, switching alpha, diagonal-only energy, and E12+.125g. Nonzero bounded-disturbance equilibrium disproves unconditional origin convergence. Minimum dwell prevents Zeno-clock gaps. These often refute proof/formula reuse, not every possible invariant for the changed system.

Primary literature status checked19October2026: Fiacchini/Alamir, https://arxiv.org/abs/1708.04797, describes Minkowski-set operations for constrained linear control invariance; Anevlavis/Liu/Ozay/Tabuada, https://arxiv.org/abs/2107.08566, describes implicit controlled-invariant representations. Abstracts inspected only. They establish that set addition/implicit representation are established approaches; neither abstract supplies this particular fixed saturated sampled-policy certificate. No novelty claim or full literature review.

PM gate GO: source-faithful strict expansion plus explicit active witness justify a bounded membership/symmetry consumer experiment after breadth. Physical calibration, arbitrary lag uncertainty, sensor delay, floating arithmetic and hardware remain outside the model. Quality rubric4/4/4/4/3=95/100; subjective confidence high for exact source theorem, uncalibrated for transfer/novelty.
