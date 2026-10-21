# C07: Sample-interval certificate conservatism

**NOT REVIEWED — inventory card only.**

Question: How much allowable sampling range is lost to Bernstein/LDL certificates compared with true held-map stability on the same normalized plant?

Prior work (investigated): Exact rational producer and Lean checker support interval energy decrease; a wider double-integrator variant reaches h=33/50 with smaller margin.

Obstacle: Failure of the chosen common quadratic or Bernstein coefficient test is not instability.

Candidate crossover: Use polynomial approximation subdivision and common-metric geometry to separate representation conservatism from metric conservatism.

Proposed cheap test: For the 2-state benchmark compute the exact Schur stability polynomial and compare its boundary to the stored certificate interval.

Selection reason: Distinct controls question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/README.txt
- /Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/LeanControls/BernsteinCertificate.lean
- /Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/benchmarks/double-integrator-wide.json
