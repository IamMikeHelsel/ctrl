# S05: Within-hold disturbance semantics

**NOT REVIEWED — inventory card only.**

Question: Can the fixed held-error safety theorem tolerate bounded within-hold forcing without silently reusing constant-input formulas?

Prior work (investigated): Fixed-lag execution uses held command-equivalent errors; a separate varying-response comparison handles continuous effective targets for finite envelopes.

Obstacle: Constant-flow equalities and all-time energy certificates do not automatically transfer to arbitrary forcing.

Candidate crossover: Use integral quadratic constraints or convolution-kernel L1 bounds to translate the disturbance history into a checked step residual.

Proposed cheap test: Compute the exact impulse-response sign pattern on one hold and compare constant worst-case forcing with a sign-aligned bounded forcing.

Selection reason: Distinct safety question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/README.txt
- /Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/LeanControls/HeldDisturbance.lean
- /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/adjacency-review/transient-variation.txt
