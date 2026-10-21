# S09: Common-cause failures at the proof/reliability interface

**NOT REVIEWED — inventory card only.**

Question: How can deterministic execution guarantees be composed with an explicit fault process without pretending proof success establishes a safety performance level?

Prior work (surveyed): Prior review separates functional behavior, dangerous failure frequency and architecture/validation obligations; no component reliability data or PL claim exists.

Obstacle: A per-stop exceedance probability cannot be converted to an hourly failure rate without an operational model; shared causes defeat independent multiplication.

Candidate crossover: Borrow fault-tree cut sets and adversarial causal graphs to make shared sensor/clock/power assumptions visible.

Proposed cheap test: Build a minimal symbolic two-channel fault model with one shared cause and show the gap between independent and common-cause failure calculations.

Selection reason: Distinct safety question with source-linked obstacle and small test; wildcard transfer reserved for exploration. Subjective rubric, not success probability.

Sources:

- /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/adjacency-review/performance-level-review.txt
