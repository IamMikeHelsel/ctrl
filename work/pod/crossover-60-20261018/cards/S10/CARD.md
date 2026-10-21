# S10: Population uncertainty to a conditional envelope

**NOT REVIEWED — inventory card only.**

Question: What evidence contract converts multi-unit, repeated-condition stopping data into a calibrated uncertainty set while retaining separate statistical and deterministic claims?

Prior work (surveyed): Existing review calls for held-out units/conditions, uncertainty-aware measurements and explicit population coverage; no hardware dataset is present.

Obstacle: Repeated measurements can share temperature and calibration errors; an empirical percentile is not an all-trajectories bound.

Candidate crossover: Use hierarchical set calibration and adversarial holdouts by unit/condition rather than row-wise random splits.

Proposed cheap test: Create a small exact synthetic shared-bias example showing row-wise replication reduces naive uncertainty while leaving between-unit uncertainty unchanged.

Selection reason: Distinct safety question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/adjacency-review/performance-level-review.txt
- /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/adjacency-review/transient-variation.txt
