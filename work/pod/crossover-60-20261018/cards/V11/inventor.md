# V11 cross-discipline inventor

AI-written research; inherited root model, exact model identifier unavailable. Root owns timing and the PM decision. Only V11 inventor artifacts were changed. No source, approved challenge, physical sensor, or remote resource was modified.

## Source and missing contract

Read the V11 roster/card, `.agents/teamwork/explorer_survey_vision_1/handoff.md`, `/Users/mike/Dev/ctrl-research-notebook/ControlsLean/Estimation/InformationFilter.lean`, and the scalar update definitions in its `ScalarKalman.lean` dependency. The survey is proposal/context evidence, not a verified global-geometry or novelty result. Its broader claims are not imported here.

The information-filter source proves two-sided inverse algebra in an arbitrary ring. It does not define a measurement vector or posterior mean, prove a geometric outlier predicate sound, establish statistical independence, or bound actual estimation error. The scalar source defines an algebraic variance expression; interpreting that expression as the variance of a physical random error needs assumptions outside the displayed algebra. Positive covariance, an observation model, and truth-bearing noise/outlier contracts are additional obligations. Our linear measurement toy and additive information mean below are explicitly added models, not existing source theorems.

## Three transfers, with falsifiers

**1. Robust set membership instead of covariance-as-error.** Maintain a sound prior set S0 and the union Q of all joint measurement branches consistent with an explicit fault budget. For at most f faulty observations, a branch imposes the noise strips for a candidate set of at least n−f inliers. Keep every feasible branch; require nonemptiness before using Q. A proposed additive-information mean μ is admitted with deterministic bound B only if

    sup{x in Q} ||μ−x||∞ ≤ B.

Truth coverage x*∈Q follows from the supplied prior/noise/fault assumptions, not from nonemptiness alone. Geometric optimization and inverse algebra remain separate obligations. This preserves an actual-error implication and allows biased/correlated but bounded inlier errors; it needs no Gaussian interpretation. Falsifiers: an explicitly admissible world outside the reported error ball, dropping a feasible branch, replacing a joint branch by independently selected marginal witnesses, or assuming the physical fault budget from a nonempty fit.

**2. Error-correcting geometry.** Map a state difference Δx to its measurement difference HΔx. In the noiseless model, if two explanations each tolerate f faults, their measurements can disagree on at most 2f rows. Therefore support(HΔx)>2f for every nonzero Δx prevents this ambiguity. This transfers the distinction between redundant data and distinguishable states. For H with rows (1,0),(0,1),(1,1), one fault permits the same observation vector (1,0,0) to arise from (0,0),(1,0), or (1,−1). Adding row (1,2) makes every pair of rows independent; a nonzero Δx annihilates at most one of four rows, so its support is at least three. This gives exact one-fault distinguishability at zero noise, not zero error at nonzero noise.

Preservation requires a common fixed linear observation map, a prior domain and faults counted by actual observation origins. Duplicating a feature does not create another independent origin or justify keeping a one-fault assumption if that origin is corrupt. Nonlinear pose charts, calibration error and linearization remainder need their own enclosure. The critic supplied a sharp nonzero-noise counterexample: with observations (0,−4ε,ε,−ε), states (0,0) and (6ε,−4ε) each have only one fault. Consequently the four-row geometry cannot universally force diameter below 6ε or radius below 3ε. An information inverse smaller than this is not a deterministic certificate.

**3. Unexpected transfer: a transaction may carry information without permission to move the estimate.** Treat additive information as a proposed update and the set-based error enclosure as its admission certificate. If the certificate fails, retain the prior estimate and its existing bound; do not report a covariance-derived error improvement. This is a proof-carrying abstention interface, not a new estimator optimality claim.

Without a truth-bearing measurement restriction, a prior interval [μ−r,μ+r] and an update displacement δ give the sharp worst error r+|δ|. An already-tight radius r therefore cannot survive a nonzero update merely because the measurement geometrically overlaps the prior. If a separately declared extra margin β is permitted, scalar information weight λ obeys

    λ ≤ Y β / (|z−μ|−β),  when |z−μ|>β,

because δ=λ(z−μ)/(Y+λ). This can cap untrusted information's effect, but it explicitly spends a larger bound. It is not a claim that the original radius improved. Falsifiers: confusing numerical precision with permission, silently enlarging B, or accepting an existential close world rather than bounding all retained worlds.

## Exact experiment: geometry plus additive information

`inventor_geometry.py` uses exact rational arithmetic, prior box [-1,1]^2, H rows x,y,x+y,x+2y, observations z=(1,0,0,0), bounded inlier residual ε=1/100 and at most one faulty original observation. The branch algorithm intersects all triples of noise strips with the prior and enumerates exact polygon vertices. Every individual strip intersects the prior; that weak geometric rule would admit all observations.

For three rows there are three feasible branches and no row belongs to every inlier subset. For four rows exactly one branch survives: rows 2,3,4. Its uniformly bounded-residual rows can safely feed the additive update. This is about their residual validity over Q, not infallibility of their sensor hardware.

Use prior information I and prior mean zero. Give row 1 weight 10000 and the other rows weight 1. The all-data information matrix is positive definite and its inverse is checked exactly, yet the resulting mean has actual L∞ error greater than the prior radius 1 at an explicitly admissible world. The computed sharp errors over Q are:

| admitted geometry | all-data candidate worst error | certified-row candidate worst error |
|---|---:|---:|
| three rows, one fault | 306001/300050 > 1 | 1 (no certain row; retain prior) |
| four rows, one fault | 892503/875150 > 1 | 1/50 |

For the four-row case, the candidate using the three certified rows has mean zero. Its deterministic error radius is exactly 1/50, established independently of its information inverse. The all-data mean is approximately (0.999829,−0.428498); the admissible world (−.02,.01) makes its x error exceed 1. All inverse identities still hold. Thus this is an actual-error failure, not merely a complaint about covariance interpretation.

The positive radius has a direct inequality derivation, beyond vertex enumeration. For this observation vector, if ε<1/4, any triple containing row 1 is impossible: row 1 forces x≥1−ε, whereas any two other rows imply |x|≤3ε. The only branch uses rows 2,3,4; |y|≤ε and |x+y|≤ε imply |x|≤2ε. The extremum (2ε,−ε) attains radius 2ε. At ε=1/4, alternative branches appear—for example (.75,−.25) fits rows 1,2,4—so the threshold is substantive. Exact checks cover ε=.01,.2,.249,.25,.3,1/3. This is a fixture-specific admission threshold, not a universal vision threshold.

## Further negative controls

`inventor_budget.py` checks a scalar biased measurement z=1/2 with prior precision 1 and measurement precision 10^6. A broad geometric innovation gate passes; the candidate moves to 500000/1000001 while inverse information drops to 1/1000001. At true x=0, actual error becomes nearly 1/2. Repeating the same origin 10 or 100 times further shrinks the inverse while retaining essentially the same bias; duplicates do not add truth-bearing constraints.

The declared margin example r=1, β=.1, Y=1 and z=.5 gives λ≤1/4, candidate displacement .1 and exact worst error1.1. This is an explicit optional extension, not preservation of radius1.

Finally, z=(1,0,1,0) has a nonempty one-fault explanation at false world (1,0), although true world (0,0) requires two faults. Thus nonempty geometry cannot certify the physical fault-count assumption. Empty Q must cause abstention/model-diagnosis, but nonempty Q does not prove the assumptions true.

All calculations here are exact rational witnesses and source-linked derivations, not inventor kernel proofs. The positive polygon bound also has the direct inequality argument above. Neither synthetic linear localization nor a matrix identity establishes a calibrated camera-pose error bound. Both own scripts pass Ruff. No package installation occurred.

`inventor_farkas.py/json` contains exact certificate arithmetic and several fixture assertions, but **failed the PM's acceptance review as a branch-verification consumer**. Each intended rejected branch has nonnegative rational multipliers combining its constraints to 0≤−1+3ε or 0≤−1+4ε. However, `evaluate(certificate, epsilon)` has no branch argument and looks up constraints globally. A certificate using row 1 can therefore be misassigned to the feasible branch {2,3,4} and still pass its arithmetic check. The script must not be described as a sound branch-rejection adapter.

The purported missing-branch and duplicate-origin “rejections” are static assertions that two sets or counts differ; no consumer takes such a malformed manifest and rejects it. The negative-multiplier arithmetic check, zero-RHS strictness check at ε=1/4, and fixed-matrix candidate substitution test are narrower checks that do execute. Even the latter does not establish a general data-to-information-matrix binding. The explicit feasible point (.75,−.25) at the threshold remains valid. These distinctions correct the earlier overstatement. The failed prototype, JSON, and output are preserved unchanged; lint success does not repair semantic binding.

Minimal next-block fix: make the consumer accept the complete manifest, trusted observation records with unique origin IDs, and branch-specific certificates. Generate the required inlier subsets from those unique IDs; require exact manifest coverage. For each rejected branch, reconstruct its allowed inequalities from that branch plus the prior, reject every multiplier referencing another branch's row, and only then check nonnegative weights, zero combined normal, and strictly negative combined RHS. Retained branches need an admissible witness and candidate-bound certificates over those same inequalities. Reconstruct Y and η from the declared admitted observations and weights, then bind the returned mean to Yμ=η. Mandatory end-to-end mutation: relabel the row-1 contradiction certificate as branch {2,3,4}; the corrected consumer must reject it while retaining that branch's zero-state witness.

## Proposed gate and next action

**GO** for a narrow admission adapter with explicit truth coverage, nonempty joint branch union, a shared candidate/geometry state representation, and a universal actual-error bound. Keep the information update algebra, but make acceptance depend on the independent enclosure. The next test should formalize the four-row ε<1/4 rejection and 2ε bound, bind the actual additive mean, and reject mutations that replace universal coverage with overlap, drop a branch, or count cloned observations as new fault origins. A nonlinear vision extension additionally needs a calibrated residual/linearization contract.

**NO-GO** for covariance shrinkage as an actual-error certificate, geometric compatibility as proof of honest noise, or silently changing the requested error budget. **HOLD** physical pose guarantees and statistical posterior claims until the corresponding observation and noise assumptions are supplied and checked.

Quality after PM rejection: faithfulness 4/4, reproducibility 4/4, discriminatory value 4/4, critique 3/4, actionability 2/4 = 17/20 (85%). The exact estimation-error fixtures remain useful; the prototype is not an accepted branch-verification consumer. Subjective confidence is high in the rational fixtures, lower in the unimplemented adapter contract, and uncalibrated for camera-model adequacy or general robust-estimator performance.
