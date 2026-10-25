# A small exact transport certificate

This prototype checks finite transport witnesses using exact rational arithmetic. It produces a global lower bound, the submitted coupling's cost, and an additive gap. A companion Lean file proves the underlying weak-duality inequality. It does not prove that the Python checker implements that theorem, replay these individual witnesses inside Lean, or certify robot motion.

The source motivation is [partitioned optimal transport for multi-agent distribution matching](https://arxiv.org/abs/2609.38960). A restricted feasible coupling still bounds the unrestricted objective from above. The prototype also follows the useful separation between candidate search and certificate checking illustrated by [CP-Cert](https://arxiv.org/abs/2609.03222). It reproduces neither paper's complete algorithm or performance results. The certificate principle is standard; no mathematical novelty is claimed.

## Statement and boundary

For costs `c[i,j]`, nonnegative coupling `p[i,j]`, and exact marginals `a[i]`, `b[j]`, require:

```text
sum_j p[i,j] = a[i]             sum_i p[i,j] = b[j]
u[i] + v[j] <= c[i,j]           for every edge, including unused edges
L = sum_i a[i] u[i] + sum_j b[j] v[j]
U = sum_ij p[i,j] c[i,j]
L <= global optimum <= U
gap = U - L = sum_ij p[i,j] (c[i,j] - u[i] - v[j]) >= 0
```

The checker accepts a suboptimal coupling while reporting its gap. It labels the coupling globally optimal only when the exact gap is zero. Floats, invalid rationals, negative flows, malformed dimensions and inconsistent marginal masses are rejected. Total mass may differ from one, but it must be positive and balanced. Costs may be negative; the argument is finite LP duality, not a metric assumption.

The global lower bound is especially important for partitioning. A dual witness checked only on permitted block edges can overstate the quality of a restricted assignment. This checker checks every cost entry. It has no block mask that could silently change the problem being certified.

## Observed results

The deterministic study uses source coordinates `[0, 1, 10, 11]`, target coordinates `[1, 2, 11, 12]`, squared distances and uniform mass. These are synthetic unitless coordinates.

| Submitted assignment | Certified interval | Exact gap | Exhaustive optimum |
|---|---:|---:|---:|
| Aligned | [1, 1] | 0 | 1 |
| Suboptimal within blocks | [1, 2] | 1 | 1 |
| Crossed blocks | [1, 101] | 100 | 1 |

A separate rectangular example splits mass across three targets and certifies `[1/4, 1/4]`. An independent quarter-grid enumeration checks that example in the unit tests.

For 24 seeded integer cost matrices of sizes 2–5, a brute-force assignment oracle examined all permutations. All 912 submitted candidate intervals enclosed the independently computed optimum. A difference-constraint witness generator returned exact zero-gap duals for the optimum in each instance and rejected all 884 strictly suboptimal assignments as candidates for a tight dual. Tied optima were allowed. This oracle checks tiny uniform assignment problems; it is not a general transport solver or a proof that every checker input is handled correctly.

Six adversarial study cases were rejected: missing flow, forged dual, floating-point cost, negative flow, unequal total mass and wrong matrix shape. The tests additionally cover malformed rational values, column conservation, zero-mass rows, nonunit total mass, and every 2×2 matrix over a three-value cost alphabet. Eighteen tests passed in 0.05 seconds in the recorded local run.

## Reproduction

From the repository root:

```sh
uv run python experiments/research/transport_certificate.py --output work/research/2026-10/transport-results.json
uv run pytest -q tests/test_transport_certificate.py
uv run ruff check --no-force-exclude experiments/research/transport_certificate.py tests/test_transport_certificate.py
uv run ruff format --check --no-force-exclude experiments/research/transport_certificate.py tests/test_transport_certificate.py
```

From `lean/`:

```sh
lake env lean Research/TransportCertificate.lean
```

That command succeeded. `finite_transport_weak_duality` and `finite_transport_candidate_gap` each reported only `propext`, `Classical.choice`, and `Quot.sound`. The second theorem assumes an upper bound on a candidate cost; candidate feasibility is explicitly a separate obligation. The JSON artifact includes the Python source hash and full synthetic witnesses so a later run can check provenance.

## Proposed utility and next falsifier

This could make an assignment component's quality visible without trusting the search algorithm. A future adapter could accept a fast block assignment and export a checked gap before deciding whether to spend time on a global solve. The present experiment has not measured an advantage in solve time, memory, task success or robot safety.

The next useful step is to replay the rational witnesses inside Lean and test whether useful dual gaps survive realistic costs and partition sizes. If the gaps are routinely too wide, rational reconstruction fails, or checking exceeds the saved solver time, the proposed integration should be deferred. Motion dynamics, collision constraints, timing, sensor uncertainty and finite-precision execution remain separate obligations.

AI disclosure: Codex drafted the survey, experiment, tests, Lean module and this note. The numerical study and direct Lean compilation were run locally. No external deployment, physical robot test or novelty assessment was performed.
