# V06 domain review: exact cycle certificates

Model: inherited root model; exact runtime identifier unavailable. AI-generated research and proofs. Original sources remain unchanged. This is a small constructed rotation-graph fixture, not a replay of SE-Sync software or a claim about physical pose truth.

## Source and question binding

The local vision handoff catalogues SE-Sync; it does not contain an inspected implementation or a prior fixture certificate. The frozen question asks for an independently checkable global-optimality certificate for an inconsistent small relative-pose graph after gauge fixing.

The [primary SE-Sync technical report](https://arxiv.org/abs/1612.07386) derives an SDP relaxation, a posteriori certificates and sufficient conditions for exactness. Its orthogonal relaxation requires special-orthogonal membership to recover the original rotation problem. Its connected-graph assumption matters to translation gauge. These are conditional results, not a blanket claim that every noisy graph has a tight relaxation. The [author's correction](https://david-m-rosen.github.io/files/SESync_correction.pdf) repairs the proof of theorem12 while retaining the theorem statement; the original argument mishandled a constrained singular-value optimization. The elementary certificates here are checked directly, independently of that corrected proof.

## Exact boundary fixture

Three nodes, unit rotational weights, directed measurements M01=I, M12=I, M02=-I. These are all proper SO(2) rotations. Anchor R0=I. The actual matrix objective is

F = ||R1-I||F² + ||R2-R1||F² + ||R2+I||F².

For proper rotations Rj=rotation(cj,sj), with cj²+sj²=1,

F = 6 + 2[(1-c1+c2)²+(s2-s1)²].

Thus F≥6 globally. R1=rotation(1/2,sqrt(3)/2), R2=rotation(-1/2,sqrt(3)/2) attains6. The conjugate pair with both sine coordinates negated also attains6 and remains distinct after anchoring. This is genuine nonuniqueness, not an unfixed common rotation.

The connection Laplacian is [[2,-1,1],[-1,2,-1],[1,-1,2]]. Subtracting node multipliers1 gives S=bbᵀ, b=(1,-1,1). The full slack S⊗I2 has rank2, nullity4. Complementary slackness is I-R1+R2=0. All-I is stationary at cost8: its corresponding slack has a direction (1,0,-1) with quadratic value-2. Stationarity therefore fails the PSD certificate and does not imply global optimality.

## Tests and proof binding

- `domain_cycle.py` uses exact Fraction arithmetic in Q(sqrt(3)), checks the physical SO(2) matrices, every edge cost, two optimum candidates, rational slack factor and the stationary negative witness. `domain_cycle.json` serializes these checks. No numerical optimizer is trusted.
- `domain_certificate.lean` has12 declarations, including the actual Frobenius expansion, global bound, algebraic attainment, distinct gauge-fixed candidates, and a surjective parameterization lemma for every real2x2 matrix satisfying RᵀR=I and detR=1. `global_matrix_bound` therefore quantifies over arbitrary proper matrices, not only assumed scalar coordinates. The final compilation passes with only propext, Classical.choice, Quot.sound. An initial failed tactic attempt is retained separately.
- Root's independent rational interior fixture is stronger for uniqueness: the closing measurement rotation(-44/125,117/125), optimum rotations(4/5,3/5) and(7/25,24/25), optimum12/5. `domain_pm_bridge.lean` connects root's scalar SOS and uniqueness theorem to this actual matrix objective, using the proved proper-matrix parameterization. Its final compilation status is recorded in `domain_pm_bridge.log`.

## Interpretation and limits

The useful crossover is an optimization dual certificate converted into an elementary polynomial sum-of-squares identity and then checked by Lean. It preserves the exact weighted objective and SO(2) feasible set. It would break if a transpose convention, Frobenius factor2, weight, measurement, reflection allowance or gauge changed without regenerating the identity. The π fixture proves certification does not imply uniqueness; the rational interior fixture separates the two properties. Neither says the optimum equals the true physical poses.

The domain fixture is rotation-only. Parent's separate full SE(2) extension must include actual translation residuals and an anchor for translation; rotation-only optimality alone does not certify an arbitrary coupled translation problem. Disconnected graphs require a gauge per connected component. The examples make no generic tightness claim and do not test a SE-Sync implementation.

Evidence level: exact independent-arithmetic candidate/certificate checks plus kernel-checked fixture theorems. Mathematical novelty: none claimed; duality and SOS are established mechanisms. Suggested decision: GO for a small certificate-export/check interface with explicit objective binding, HOLD any broad or implementation-level claim. Precise next test: mutate an edge orientation, weight and reflection constraint and require the certificate checker to reject or explicitly rebind each case. Quality grade: 4/5 for the bounded fixture; subjective confidence high for the compiled statements, separate from coverage of full SE(d).

Independent critic replay subsequently accepted all12 declarations in the π module with permitted axioms, including the arbitrary-matrix binding. The root dependency was revised only to replace expensive proof tactics; its seven statements now compile clean. The new matrix/vector bridge compilation is a separate acceptance step, not inferred from those results.

## Final local bridge acceptance

Both new bridge modules now compile exit0, four declarations each, with only propext, Classical.choice and Quot.sound. `domain_full_bridge.lean` defines the full anchored directed SE(2) objective using actual matrices and Fin2 translation vectors:

Ffull = Frotation + ||p1-(1,0)||² + ||p2-p1-R1(3/5,4/5)||² + ||p2-(1,1)||².

For every proper R1,R2 and every p1,p2, it proves Ffull≥12/5. Equality forces R1=rotation(4/5,3/5), R2=rotation(7/25,24/25), p1=(1,0), p2=(1,1); that candidate attains equality. Both gauges are fixed by R0=I,p0=0. This closes the matrix/vector binding for this declared full SE(2) fixture; it does not generalize to arbitrary graphs or claim an implementation audit. The π rotational nonuniqueness theorem concerns its separately declared fixture and is unchanged.

All20 domain declarations are locally accepted; the independent critic has accepted the first12 and is replaying the final8 at this checkpoint. Root's seven scalar dependency declarations also passed my independent compilation. Failed first bridge attempts remain in the attempt1 logs: one missing noncomputable marker, one simplification-order failure. Neither failed artifact is accepted as evidence.

Reproduce from `/Users/mike/Dev/ctrl/lean`, setting `C=../work/pod/crossover-60-20261018/cards/V06` in the shell:

```sh
lake env lean -R "$C" -o "$C/pm_cycle.olean" "$C/pm_cycle.lean"
lake env lean -R "$C" -o "$C/domain_certificate.olean" "$C/domain_certificate.lean"
LEAN_PATH="$C" lake env lean -R "$C" -o "$C/domain_pm_bridge.olean" "$C/domain_pm_bridge.lean"
LEAN_PATH="$C" lake env lean "$C/domain_full_bridge.lean"
```

From repository root, the exact arithmetic replay and scoped hygiene checks are:

```sh
uv run --no-project --python /usr/local/bin/python3 python work/pod/crossover-60-20261018/cards/V06/domain_cycle.py
uv run ruff check work/pod/crossover-60-20261018/cards/V06/domain_cycle.py
uv run ruff format --check work/pod/crossover-60-20261018/cards/V06/domain_cycle.py
```

These isolated research artifacts do not modify the public CLI or approved Lean challenges. Whole-repository checks are root's integrated handoff responsibility and are not claimed from these scoped checks.
