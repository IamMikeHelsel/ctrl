# C03 inventor: joint moment admission, retained-history budgets, and bounded-density transport

AI-assisted research; inherited root model, exact identifier unavailable. Source read: `/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/admission-04/analyst/report.txt`, plus frozen roster. The source already has the sharp first-zero-acceleration bound and a separately declared feasible0.6m reference. This work does not repair its rejected old endpoint or change its accepted task. It investigates necessary admission checks for full endpoint states.

## 1. Reachability as a dual moment problem

For snap u=j', the endpoint acceleration, velocity and position are different weighted moments of the same jerk history. Separate scalar bounds form an outer box, not the joint reachable set. A linear combination of endpoint residuals corresponds to a polynomial time kernel; integrating its absolute value supplies a compact necessary inequality. This is an exact map of the kinematics, assuming absolutely continuous jerk and the specified almost-everywhere snap bound. It does not establish sufficiency or plant tracking.

A sharp normalized diagnostic starts at `(q,v,a,j)=0`, uses T=1, J=S=1, and requires terminal jerk0. The proposed endpoint is `(0,−1/16,1/8,0)`. Each requested coordinate is independently attainable: half a positive triangular jerk gives a=1/8, half its negative gives v=−1/16, and the zero path gives q=0. These are different admissible histories, not a single accepted reference. All values lie strictly inside their individual coordinate ranges.

Nevertheless every jointly admissible history obeys

`a(1)−2v(1)=∫₀¹(t−t²−3/16)u(t)dt ≤1/16`.

Indeed integration by parts gives kernel `t−t²`, and subtracting3/16 changes nothing because `∫u=j(1)−j(0)=0`. The factorization `(t−1/4)(3/4−t)` determines its sign and its absolute integral is1/16. The request has value1/4 and is impossible. Snap−1,+1,−1 on the quarter/half/quarter intervals attains the bound, with endpoint `(−1/64,−1/32,0,0)`; its jerk magnitude is at most1/4, so the declared J=1 also holds.

For arbitrary retained initial state and endpoint jerk, put `A=aT−a0`, `V=vT−v0−a0 T`. The same kernel after time scaling gives the necessary gate

`|A−2V/T−(3T/16)(jT−j0)| ≤ S T²/16`, for T>0.

It ignores the jerk amplitude limit, position corridor, velocity/acceleration limits and position endpoint, so passing this gate cannot admit a trajectory. It is sharp in the equal-endpoint-jerk diagnostic; no sharpness is claimed for arbitrary unequal jerks.

Concrete source-history probe: use the actual execution state `a0=51/20`, `v0=2601/8000`, `j0=10`, and test a hypothetical terminal v=a=j=0 after T=11/25. The left side is8541/1760, the bound121/25, excess113/8800>0. Thus stopping by0.44s after execution is impossible even before checking q. The source's accepted horizon249/200 is unchanged; this is a shorter-deadline diagnostic, not a failed replay of the accepted task.

Falsifier: an explicit absolutely continuous jerk satisfying all the diagnostic bounds but violating the support inequality would refute the derivation. The exact attaining reference checks constants and signs. Next useful test is a small library of mixed polynomial kernels, including q, with independently checked integrals and explicit state/clock binding.

## 2. Latency as a state-dependent resource budget

Map deadline admission to a scheduling ledger whose pending work changes the state while the new request waits. Latency consumes both clock time and future control authority; it cannot be represented only by subtracting a number from the deadline while retaining the old state. This preserves the commanded prehistory and causal information: the new goal cannot act before arrival or execution.

The source's specified latency behavior is constant old jerk+10 for ell=1/200. Propagating its arrival state `(5/192,5/16,5/2,10)` exactly gives execution state `(44217/1600000,2601/8000,51/20,10)`, including every position/velocity/acceleration increment. The existing first-zero-acceleration bound consequently charges two latency terms in time measured from arrival under this particular hold policy. This is not a universal latency law for different pending commands.

Falsifier/negative control: applying the mixed gate after resetting a,v,j to zero makes that inequality pass vacuously, but evaluates a different initial-value problem. A stale or mismatched state timestamp is therefore a semantic failure even when the algebraic inequality is correct. If latency is uncertain, admission must cover the full reachable execution-state/remaining-time pairs, preserving their correlation rather than mixing independent marginal extrema casually.

Precise next test: make the admission certificate bind arrival timestamp, execution timestamp or delay interval, the actual queued reference polynomial, full(q,v,a,j) execution state, endpoint and deadline. Replay a delayed commit against the changed execution state and require rejection or recomputation. This concerns reference admission only; actual actuator/controller states remain an additional handoff obligation.

## 3. Unexpected transfer: bounded-density transport, and why PSD moments can lie

For the normalized diagnostic, transform snap into the nonnegative measure `dμ=(u+1)dt`. Endpoint jerks0 imply total mass1, and |u|≤1 means **density between0 and2**. At terminal a=0, the mass mean is1/2, and its second moment is `1/3+2v`. Thus the motion problem becomes a constrained distribution of mass in time. This representation preserves snap authority only if the density cap is retained.

Dropping the cap admits a Dirac mass at1/2. Its moments `(1,1/2,1/4,1/8)` have positive-semidefinite rank-one Hankel matrices and correspond formally to endpoint `(−1/48,−1/24,0,0)`. But a Dirac mass cannot equal `(u+1)dt` for bounded u; the apparent reference contains an impulse. The mixed bound also rejects it: a−2v=1/12>1/16. Moment positivity alone is therefore an unsound sufficient-admission criterion.

Retaining density≤2 recovers a sharp transport bound. With `h(t)=(t−1/2)²−1/16`, the negative region is[1/4,3/4]. Pointwise, h times the density is at least2h there and at least0 outside. Since total mass is1, integration gives

`∫(t−1/2)²dμ ≥1/48`.

Equality is attained by density2 on[1/4,3/4] and0 elsewhere. Its moments are `(1,1/2,13/48,5/32)`, giving the actual sharp velocity lower bound `v≥−1/32` when a=0. This is the same physical constraint seen through a different representation, with a useful new falsifier: replace bounded density by arbitrary positive mass and the admission problem changes.

Next test: any proposed moment/SDP gate must encode density domination, not merely moment positivity and endpoint equalities. Solver output would need an independently checked certificate; no numerical SDP verdict is used here.

## Evidence and decision proposal

`inventor_moments.py/json` checks exact polynomial integrals, separate-coordinate witnesses, the sharp mixed witness, source-history shorter-horizon rejection, and latency propagation. `inventor_density.py/json` checks the false relaxed moments and sharp density-capped moments. Continuum integration-by-parts and pointwise bounds are hand proofs, not Lean trajectory theorems; finite samples are not substituted for them. Original files and approved challenges are unchanged.

Proposed GO: develop a small mixed-moment rejection certificate tied to complete retained state and clock. Proposed NO-GO: treat a componentwise box or unconstrained PSD moment relaxation as sufficient admission. HOLD physical safety claims until reference feasibility is connected to the actual plant and actuator assumptions. No new planning-method novelty is claimed.

Quality rubric: faithfulness4, reproducibility4, discrimination4, critique4, actionability3 =19/20. Subjective confidence98% in the scoped algebra; the general sufficient admission problem remains unresolved.
