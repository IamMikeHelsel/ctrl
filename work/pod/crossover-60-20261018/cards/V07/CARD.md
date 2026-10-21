# V07: Complete minimal absolute-pose candidates

**NOT REVIEWED — inventory card only.**

Question: Can a P3P minimal solver produce all physically admissible camera poses for a three-point instance with a checkable real-root certificate?

Prior work (catalogued): Survey names P3P in its minimal-solver transfer discussion; no P3P implementation or polynomial derivation checked.

Obstacle: Numerical action-matrix eigenvalues are not automatically complete exact roots; singular and repeated-root cases need treatment.

Candidate crossover: Transfer algebraic root isolation and certificate checking from exact mathematics.

Proposed cheap test: Choose rational geometry, derive its range equations, isolate roots and reconstruct each pose; test collinear input rejection.

Selection reason: Distinct vision question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Dev/ctrl/.agents/teamwork/explorer_survey_vision_1/handoff.md
