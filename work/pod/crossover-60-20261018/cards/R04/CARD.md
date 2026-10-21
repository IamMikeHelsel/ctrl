# R04: Conditional scheduler progress

**NOT REVIEWED — inventory card only.**

Question: Under what feasible-task margin, candidate coverage, computation bounds and request-rate assumptions must the executor eventually accept a request?

Prior work (surveyed): Addendum explicitly separates sound acceptance from progress and lists needed premises.

Obstacle: An always-reject checker is sound but useless; a finite candidate search is not completeness.

Candidate crossover: Fair scheduling and temporal-logic liveness certificates.

Proposed cheap test: Small discrete scheduler model with a feasible execution slot; compare bounded exhaustive slot coverage to starvation under repeated supersession.

Selection reason: Distinct robotics question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/robot-motion/stabilization-research-addendum-2026-10-18.md
