# R06: World-frame derivative transport

**NOT REVIEWED — inventory card only.**

Question: Can world-frame output constraints be preserved when body motion, frame/calibration updates and coupled robot kinematics transform an actuator reference?

Prior work (surveyed): Addendum identifies frame derivative, calibration, singularity and coupled dynamics obligations; no proved multi-axis extension.

Obstacle: Componentwise limits do not imply Cartesian bounds; rotating-frame terms and singularities can amplify error.

Candidate crossover: Differential geometry covariant derivatives and robust Jacobian bounds.

Proposed cheap test: Two-dimensional rotating base with constant body-frame vector: calculate nonzero world velocity/acceleration and expose an omitted transport term.

Selection reason: Distinct robotics question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/robot-motion/stabilization-research-addendum-2026-10-18.md
