# S06: Own-state quantization and execution uniqueness

**NOT REVIEWED — inventory card only.**

Question: Can existence and uniqueness be established for the sampled controller with deterministic state-dependent quantization rather than prescribed error sequences?

Prior work (investigated): Uniqueness is proved for prescribed h,e,d; a nominal ideal-rounding theorem is separate and does not supply the requested uncertain execution claim.

Obstacle: An arbitrary bounded error sequence and a deterministic quantizer are different closed-loop interfaces.

Candidate crossover: Use hybrid transition systems: evaluate quantization at sample boundaries, then solve a unique smooth held flow.

Proposed cheap test: Write the deterministic sample recurrence and check that a tie-breaking convention yields a unique next state even at quantizer boundaries.

Selection reason: Distinct safety question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/README.txt
- /Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/LeanControls/ExecutionUniqueness.lean
- /Users/mike/Dev/ctrl-research-notebook/research-notebook/lean-controls/LeanControls/Quantized.lean
