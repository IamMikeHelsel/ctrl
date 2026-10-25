# Perception, data and estimation: initial source triage

As of 2026-10-21. The primary window is 2026-08-21 through 2026-10-21, inclusive. All eight records in [perception-data.json](perception-data.json) have a verified arXiv v1 date inside that window. These are preprint dates. Relevant theorem, method and limitations passages were inspected; none of these papers has been independently reproduced or machine-checked here. This bounded survey is not exhaustive or a peer review. Search, triage and this note are AI-assisted.

| Priority | Source | Math × physical interface | First useful question |
|---|---|---|---|
| P1 | [PD-01: CP-Cert](https://arxiv.org/abs/2609.03222) | Convex duality × rigid geometry | Can a numerical result become an exact replayable witness? |
| P1 | [PD-02: partitioned transport](https://arxiv.org/abs/2609.38960) | Finite transport × fleet motion | Which assignment and contraction assumptions survive a cycle? |
| P1 | [PD-03: feedback evaluation](https://arxiv.org/abs/2609.02811) | Estimation statistics × sensing cadence | Does the offline ranking select the better controller input? |
| P2 | [PD-04: CoSMO](https://arxiv.org/abs/2610.18321) | Coverage sets × semantic clearance | Where do detection, discovery and motion break composition? |
| P2 | [PD-05: minimum-volume OTCP](https://arxiv.org/abs/2610.14907) | Transport geometry × anisotropic residuals | Is smaller uncertainty volume useful for the actual task? |
| P2 | [PD-06: NLPV observers](https://arxiv.org/abs/2609.18603) | LMI dissipation × manipulator dynamics | Does the energy bound retain initial conditions and normalization? |
| P3 | [PD-07: CyclOT](https://arxiv.org/abs/2609.13892) | Inverse consistency × proposed sensor alignment | Can a good cycle loss hide a wrong physical map? |
| P3 | [PD-08: nonlocal transport](https://arxiv.org/abs/2609.05062) | Fractional regularity × proposed scene boundaries | Does a discrete approximation retain the useful behavior? |

The strongest near-term contribution is an evidence interface: search can propose a coupling or optimization witness, while a small independent checker verifies exactly what it certifies. Existing `tools/sdp_rational_cert.py`, finite matrix proofs, and ISS algebra provide relevant starting points. This is an integration opportunity; it does not establish research novelty.

For the first transport prototype, certify mass conservation and an objective interval using exact rational primal and dual witnesses. A block-restricted feasible coupling gives an upper bound for the unrestricted problem. An unrestricted feasible dual gives a lower bound. Their gap quantifies assignment quality without claiming that the partitioned result is globally optimal. Motion, collision avoidance and tracking are separate obligations.

For a second phase, replay estimator evaluation with matched measurement schedules before adding learned perception. A better-looking prediction curve should earn its place through held-out closed-loop outcomes. Report negative results and uncertainty alongside any improvement.

One source needs a faithfulness check before transcription. From PD-06 equation (12), assuming nonnegative terminal energy and a positive quadratic lower bound, integration yields an error-energy bound containing the initial energy and division by the decay rate times the minimum eigenvalue. The displayed final bound in its Theorem 1 proof suppresses those terms. An unstated zero-initial-error or normalization convention may explain part of this, but the present survey does not resolve it. A scalar counterexample should precede any implementation based on that display.

Coverage limits: the selected evidence favors exact optimization and uncertainty interfaces. It does not cover all recent machine-vision architectures, datasets, SLAM systems, hardware platforms or physics literature. No external code or dataset was run. A source theorem is not a proof of its application model; a Python-to-Lean name association is not a semantic refinement proof; a simulation result is not physical-device acceptance. Confidence scores in the JSON express subjective triage confidence, not calibrated probabilities of success.
