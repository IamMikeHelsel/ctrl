# S07 inventor: mode semantics, positive-volume coverage, and a hidden travel mode

AI-assisted research; inherited root model, exact identifier unavailable. Sources inspected: frozen `SaturationBoundary.lean`, `TravelSafety.lean`, plus its actual dependencies `TravelGeometry.lean`, `SaturatedLag.lean`, `SaturationSector.lean`, `RobustPD.lean`, and generated `TravelQuarterLower.lean`, under `/Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/LeanControls/`.

The source already proves an important distinction. The rounded local PD budget forces clipping inactive. A separate normalized actuator-lag model has an ellipsoidal invariant containing active clipping. These are different certificates. Our tests use the latter's exact model `x'=v,v'=a,a'=-a+clamp(r0)+w`, `r0=-x0−3v0−2a0`, clamp limit1, held command and disturbance, sample interval≤1/5, and |w|≤1/100. No plant uncertainty or physical calibration is imported.

## 1. Hybrid/complementarity certificates must retain their sample origin

Map the clamp into three modes: r0<−1, |r0|≤1, r0>1. In a held interval the relevant mode belongs to the initial sampled request. Its sector gain is held with that sample. Recomputing the mode from the evolving state implements a different controller.

For a held total input U, exact cancellation of the common exponential in the source solution gives

`r(t)=r0−t(v0+a0)−U(2t+t²/2)`.

At `z0=(0,1/10,2/5)`, energy is16367/5000<12 and r0=−11/10. With w=0, clamp(r0)=−1 and the frozen sector gain is10/11. At t=1/10, the current request is−189/200, which would be unclipped if evaluated then. Nevertheless the actual held command remains−1 until the next sample. Taking h=1/5 makes the mismatch internal to an admitted held interval.

Preserved invariant: the actual source held trajectory and its original sample/sector decomposition. Breakpoint: a midhold clamp update, current-state sector gain, or mode prediction treated as an executed switch changes the input. Falsifier: compare the two commands at the exact time above; they differ by11/200. A mode-event forecast can be useful without silently changing the controller's clock.

## 2. Mode coverage is a geometric reachability question, not one cherry-picked state

Borrow coverage reasoning from experimental design and hybrid verification: intersect the proved invariant with each clamp mode and retain explicit witnesses of nonempty interior. This can detect a certificate whose budgets secretly exclude the phenomenon it advertises. It does not by itself prove invariance.

Using the exact source P, the entire axis-aligned box centered at `(0,1/10,2/5)` with radius1/200 in each coordinate lies in the invariant. Exact rational Sylvester minors show P positive definite. Every box vertex has energy≤6908201/2000000<12; convexity extends this to the box. Initial request lies in[−113/100,−107/100], so every point strictly clips negatively. This is a positive-volume set beyond the source's isolated `(0,0,1)` witness. It does not mean every point of the invariant clips—the origin does not.

For every point of that box and every held w∈[−1/100,1/100], at time1/10 the current request lies in[−19561/20000,−18239/20000], strictly inside the unclipped range. This follows from the affine request formula and all16 state-vertex/disturbance-endpoint cases. The actual sampled clamp still holds−1 for h=1/5. Thus the mode distinction is robust to a neighborhood of states and the full source disturbance interval, not a boundary coincidence.

Falsifier: perturb P, the feedback signs, disturbance placement, or sample origin and rerun the exact vertex/range consumer. Next test: require every proposed enlarged invariant to report exact intersections with all clamp modes and to bind the corresponding held-input assumptions. Mode-intersection coverage must not be presented as time occupancy or probability of clipping without a specified distribution/execution.

## 3. Unexpected transfer: quotient-state abstraction can preserve decisions while hiding travel

The request functional admits an exact reduced description: put b=v+a. Under the normalized source dynamics, b'=U and r'=−b−2U. This preserves clamp-mode evolution for matched inputs and sample times. It is a useful reduction for event prediction, but not an injective representation of the physical state.

The kernel vector k=(1,−1,1) satisfies r(k)=0, b(k)=0, and Ak=−k for the source open-loop matrix. The two active states

`z=(0,1/10,2/5)` and `z+k/2=(1/2,−2/5,9/10)`

have identical r=−11/10 and b=1/2, with energies16367/5000 and5553/1250, both below12. Under common disturbance and identical sampling, they generate the same sampled requests and clamp decisions, but their positions differ by `(1/2)exp(−t)`. Thus quotient equivalence for the control decision is not equivalence for a travel output. The hidden mode must be retained or bounded in any reconstruction.

Preserved object: exact request/aggregate dynamics and therefore sample mode decisions. Breakpoint: deducing position, clearance or safety from the quotient alone; changing lag rate from1 also breaks the displayed b'=U identity. The pair above is a concrete falsifier of injective position reconstruction. A next certificate could combine a quotient invariant with a separately bounded decaying hidden mode, keeping the output map explicit.

## Additional actuator-port audit

The source disturbance enters after the command clamp. At the active center and w=−1/100, actual held total input is−101/100, whereas moving w before the clamp gives−1. These are distinct models. A bound on the saturated command is not a bound of1 on the total forcing. At zero request, a nonzero post-clamp disturbance also cannot be absorbed into a multiplicative sector gain, since every gain times zero is zero; the source correctly uses a separate additive response.

Nor does robust invariance imply convergence to the origin: z=(1/100,0,0), w=1/100 is a nonzero equilibrium of every held interval, with energy19/25000<12. This is an exact admissible counterexample to an added origin-convergence claim, not a defect in the existing travel theorem.

## Evidence and decision proposal

`inventor_modes.py/json` uses exact Fractions for P, positive-definite minors, all16 mode cases, disturbance-order negative control, nonzero equilibrium and hidden-mode pair. Convexity, the exponential hidden-mode solution and sampled induction are hand arguments; no new kernel theorem or enlarged invariant is claimed. Root independently derived the request cancellation. No original source or approved challenge was edited.

GO for a bounded prototype that binds mode certificates to sample origin and reconstructs travel from quotient plus hidden state. NO-GO for substituting current-state mode switches, moving the disturbance through the clamp, or inferring convergence from invariance. Original broader basin question remains dependent on a fully checked invariant and output reconstruction; the existing source region already contains genuine active clipping.

Quality rubric: faithfulness4, reproducibility4, discrimination4, critique4, actionability3 =19/20. Subjective confidence98% in the exact scoped arithmetic; no physical-validation confidence is assigned.
