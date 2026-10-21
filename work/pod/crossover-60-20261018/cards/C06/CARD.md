# C06: Whole-region recovery controller comparison

**NOT REVIEWED — inventory card only.**

Question: When braking and direct feedback share the same initial box and plant assumptions, which has the larger certified recovery region per checking cost?

Prior work (investigated): A 25-step direct-feedback pilot is checked for one rate/state cell with a robust tail; the full initial-box/rate covering is not checked.

Obstacle: Single-cell wins and endpoint-only comparisons cannot establish whole-region superiority.

Candidate crossover: Borrow branch-and-bound proof reuse and abstraction refinement: refine only cells whose certificates fail.

Proposed cheap test: Identify a pair of neighboring cells sharing valid coefficient bounds and test whether one terminal certificate can cover their union.

Selection reason: Distinct controls question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/interval-checker/README.txt
- /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/direct-comparison/README.txt
