# R05: Bounded retained-history storage

**NOT REVIEWED — inventory card only.**

Question: Can the retained-event execution contract obtain a finite memory and checking-time bound while preserving all active and future commitments?

Prior work (surveyed): Prior audit states finite but unbounded histories and roughly quadratic checking work; addendum notes pruning completed events does not bound active queues.

Obstacle: Requires arrival-rate or admission assumptions; deleting future events changes the task.

Candidate crossover: Network calculus arrival curves and queueing admission applied to proof certificate size.

Proposed cheap test: Send arbitrarily dense accepted future events in one support window; derive counterexample to pruning-only bounded memory, then bound count under minimum spacing.

Selection reason: Distinct robotics question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/robot-motion/stabilization-research-addendum-2026-10-18.md
- /Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/robot-motion/execution-note/related-work-audit/comparison.md
