# S08: Diagnose mismatch while a safe fallback remains reachable

**NOT REVIEWED — inventory card only.**

Question: Can a runtime model monitor detect a specific actuator fault early enough that a certified fallback is still available?

Prior work (surveyed): The reviews distinguish logical fault detection, diagnostic coverage and complete stopping assurance; no local fault-to-fallback timing guarantee is supplied.

Obstacle: Detecting a model violation after the recoverable set has been left offers no safety guarantee.

Candidate crossover: Combine change detection with backward reachability: monitor threshold is constrained by the remaining backup reserve.

Proposed cheap test: For a declared bounded authority-loss fault, compare earliest distinguishable residual time with the latest safe brake-switch time.

Selection reason: Distinct safety question with source-linked obstacle and small test; balanced-domain selection. Subjective rubric, not success probability.

Sources:

- /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/adjacency-review/performance-level-review.txt
- /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/adjacent-controls/adjacency-review/safety-filter-review.txt
