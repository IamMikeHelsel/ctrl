# Control and safety research triage — 2026-10-21

Nine primary-source preprints were inspected within the requested 2026-08-21 through
2026-10-21 window. Dates are first arXiv submissions, with separately recorded versions;
they are not journal acceptance dates. This is a bounded survey, not comprehensive coverage.
The companion [JSON matrix](control-safety.json) distinguishes source claims from our proposed
questions, gives theorem locations, and records assumptions and falsifiers. All synthesis is
AI-assisted. No paper's experimental results were independently reproduced in this lane.

## Recommended order

| Rank | Source | Mathematics × physics | Bounded next step | Evidence boundary |
| --- | --- | --- | --- | --- |
| 1 | [CS-01: Escape-aware CBF](https://arxiv.org/html/2609.17292v1) | Reachability × actuator lag | Exact one-dimensional delay/uncertainty stopping certificate | Separate reduced model; pointwise escape is not invariance |
| 2 | [CS-02: Compute-constrained filters](https://arxiv.org/html/2610.10797v1) | Hybrid inequalities × computation delay | State a checkable per-call latency contract | Requires uniform feasible margin and a feasible answer by the deadline |
| 3 | [CS-03: VertexCBF](https://arxiv.org/html/2609.12831v2) | Convex polytopes × limited actuation | Exact residual certificates over small state cells | Learned candidates are unverified until all required inequalities are checked |
| 4 | [CS-09: Contact reach-avoid](https://arxiv.org/html/2610.17308v1) | Supermartingales × impact resets | Rational finite reset model with a probability certificate | Physical abstraction and reset distribution remain separate obligations |
| 5 | [CS-04: Koopman tube MPC](https://arxiv.org/html/2609.34844v1) | Contraction geometry × model mismatch | Certify one small physical-coordinate error tube | The metric and approximation bound cannot be assumed as the result |

The first experiment should expose one assumption at a time. For the braking example, compare
instantaneous braking with delay-aware braking under identical initial states, uncertainty
bounds and braking authority. Save every false-safe baseline case, reject invalid parameter
domains, and mutate delay/acceleration bounds to demonstrate exactly when the certificate stops
applying. There is no defensible percentage improvement to promise before this experiment.
The likely benefit is fewer false-safe classifications at the cost of more conservative stopping
decisions. Runtime, false-safe count and added clearance should be reported separately.

## Findings that change the proposed experiments

- **CS-01 has an explicit correction.** Section IV-D, Remark 2 acknowledges that using the
  future low-thrust endpoint underestimates the ramp transient. It supplies a correction or a
  more conservative current-thrust choice. Its result is explicitly pointwise escapability.
  This motivates our independent reduced model; it does not validate a quadrotor implementation.
- **CS-02 distinguishes objective tolerance from feasibility.** Section III permits a suboptimal
  objective only within the tightened feasible set. A solver returning an infeasible iterate
  before its deadline does not satisfy the contract.
- **[CS-05](https://arxiv.org/html/2609.37126v1) needs a validity monitor.** Theorem 10 is
  conditional on remaining in an engagement envelope and continued runtime feasibility.
  The estimator additionally assumes maximum capabilities occur in each observation window.
  Withholding an obstacle's strongest maneuver is a useful falsification test.
- **[CS-06](https://arxiv.org/html/2610.16326v1) lacks a safe failure path.** Algorithm 1 applies
  the last candidate if neither candidate is accepted. Treat it as an empirical proposal
  generator; add an independently justified fallback before claiming checked action selection.
- **[CS-07](https://arxiv.org/html/2609.17701v1) offers a concrete composition mechanism.** A common
  zero-assistance action satisfies all three constraints. An independent reference also prevents
  the acceptance metric from drifting with the behavior it evaluates.
- **[CS-08](https://arxiv.org/html/2609.25905v2) exposes a timing question.** Passing known upstream
  commands into downstream filters is useful, but delay and model error require additional
  bounds. Start with two small subsystems before a complete spacecraft/manipulator simulation.

## Relation to the current repository

Inspected source includes `lean/ControlsLean/Controls/MPCFeasibility.lean`,
`lean/ControlsLean/Controls/ISS.lean`, `lean/Research/LorentzConeCBF.lean`, and
`src/ctrl/robotics/contact_cbf.py`. Existing terminal-set shift proofs, dissipation bounds,
convex-combination lemmas and braking formulas are useful reusable pieces. They do not by
themselves transfer a new physical model or learned policy into a proved closed loop.

The historical 2026-10-19 report calls some work scaffolding, while the current Lorentz-cone
source contains further centroidal/Lie-derivative work. Neither the old report nor a source
docstring should determine public maturity labels: inspect the present theorem hypotheses,
build/audit results, runtime linkage and physical assumptions. This lane did not rebuild or
independently audit those pre-existing proofs.

## Gates for a write-up or animation

1. Freeze the statement, variable units, modeled domain and excluded cases.
2. Derive the relevant inequalities from the declared dynamics; do not assume the crux.
3. Reproduce a matched baseline and preserve failures with exact inputs and seeds.
4. Independently check the exported certificate and run deliberately corrupted witnesses.
5. Label a result as mathematical lemma, checked reduced model, simulation, or physical test.
6. Animate the same saved inputs and certificate boundaries. Show an out-of-domain example
   and explain why its verdict is unsupported.

A useful first animation would place instantaneous and delay-aware stopping envelopes on the
same distance axis, then vary latency and velocity uncertainty. It should teach the assumption
boundary before presenting a favorable case. No animation was rendered in this research lane.

Triage confidence: 86% (strong fit for bounded experiments; paper proofs, physical transfer and
novelty are not independently established). No production-readiness claim is supported here.
