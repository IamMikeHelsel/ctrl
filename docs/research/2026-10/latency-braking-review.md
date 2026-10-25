# Independent review of the delayed-braking example

Reviewed 2026-10-21 by a separate AI research agent. Read-only review of
`experiments/research/latency_braking.py`, `tests/test_latency_braking.py`,
`lean/Research/LatencyBraking.lean`, the saved results JSON and animation source.
No parent implementation files were changed.

**Verdict:** no arithmetic defect found in the declared one-dimensional experiment.
The model and proof boundaries are stated accurately in the inspected source. This review
supports publication as a small exact-arithmetic illustration, subject to keeping those
boundaries in the surrounding prose. It does not establish robot safety, a new mathematical
result, a complete dynamics theorem, or Python-to-Lean refinement.

## Model and mathematical check

Let `p` be the upper initial position error toward a stationary wall, `u` the upper initial
forward speed, `A` the maximum forward acceleration during reaction delay `tau`, and `b > 0`
the minimum braking deceleration. The represented trajectory uses acceleration `A` for the
entire delay, followed by deceleration `b` until rest, then holds rest. Its stopping position is

`R = p + u*tau + A*tau²/2 + (u + A*tau)²/(2*b)`.

Independent integration using average velocity times segment duration gives the same result:
reaction distance `(u + (u + A*tau))*tau/2`, followed by braking distance
`(u + A*tau)*((u + A*tau)/b)/2`. The trajectory is continuous at switching and has nonnegative
velocity until rest. Therefore checking the final position is sufficient for wall crossing
for this represented trajectory. Equality means touching the wall is permitted; this must not
be described as strict collision avoidance.

The nominal rule uses the speed estimate and immediate braking. It deliberately omits position
uncertainty, speed uncertainty and reaction delay. The two rules face the same actual worst-case
trajectory and fixed wall grid. The example consequently demonstrates a modeling omission;
it does not compare against a contemporary robust braking method.

## Independent count verification

The saved grid has `3*2*2*4*3*3 = 432` parameter combinations, each assessed against 80 fixed
wall clearances from `1/20` through `4` in steps of `1/20`: **34,560 cases**.

I independently recomputed each stopping position by trapezoidal segment integration and
counted admissible walls using the integer threshold
`max(0, 81 - max(1, ceil(20*R)))`, without calling `benchmark()` or `admits()`.
The results exactly match `work/research/2026-10/latency-braking-results.json`:

| Rule | Admissions | False admissions in this grid |
| --- | ---: | ---: |
| Immediate nominal stop | 30,480 | 2,066 |
| Bounded delay and uncertainty | 28,414 | 0 |

The 2,066 removed admissions exactly equal the nominal false admissions. This follows from the
sharp worst-case model and threshold construction; it is not an independent empirical discovery
or a measured probability of failure. The factorial grid is not a random sample. Adjacent
clearances and repeated parameter values are correlated cases, not independent trials.

Additional read-only checks covered both phase endpoints, representative interior times, held
rest after stopping, and three zero-speed/zero-delay/uncertain-speed corner contracts. The
existing focused suite passed: `uv run pytest -q tests/test_latency_braking.py` — **10 passed**.
Its independent four-interval acceleration integration is useful evidence beyond simply
re-evaluating the stopping formula. No redundant test file was added.

## Lean boundary and remaining obligations

`brake_segment_bound` derives the concave-quadratic upper bound by completing a square.
`reaction_segment_bound` bounds the reaction polynomial using nonnegative speed/acceleration.
`delayed_braking_envelope` combines those two algebraic facts. The desired envelope is derived,
not smuggled into a hypothesis, and the exact nominal counterexample is arithmetic.

The file does **not** yet prove the following:

- Absolutely continuous plant solutions satisfying derivative inequalities are bounded by the
  modeled polynomials. The comparison/integration step remains outside Lean.
- Physical sensing, delay, forward acceleration and minimum braking satisfy the supplied bounds.
- A deployed controller implements the specified switching and held-rest behavior.
- The Python `Fraction` computation or generated machine code refines the Lean expression.
- Rechecking a certificate yields recursive feasibility or an executable safe backup after a
  rejection. An already-moving robot cannot be made safe merely by rejecting its state.

The module explicitly discloses these gaps. A Lean build and axiom audit were left to the parent
agent's checkpoint; this review did not run another Lean compilation.

## Presentation and follow-up

The animation's constants agree with the saved example: `R = 273/400 = 0.6825` metres, nominal
distance `1/4`, wall `1/2`, delay `1/5`, and final stopping time `17/20` seconds. Its stop-state
clamp and phase switch match the Python trajectory. The source says rejection does not repair
an already-moving robot. Visual rendering quality was not independently reviewed here.

Suitable public wording: “On this specified exact-arithmetic grid, the delay-aware rule rejects
all 2,066 states admitted by the immediate-braking rule whose represented worst-case trajectory
crosses the wall. Lean checks the underlying polynomial envelope; physical bounds and software
refinement remain separate obligations.” Avoid “zero failures,” “100% safe,” “production-ready,”
or a general improvement percentage without the model and denominator.

For another research round, separate delay-only and uncertainty-only ablations, add variable
braking profiles and explicit boundary margins, and formalize the derivative-to-envelope
comparison before broadening the proof claim. This is useful engineering validation, not yet
evidence of mathematical novelty.

Review confidence: 92% for the arithmetic and recorded counts; no numerical confidence is
assigned to physical safety, which was not tested.
