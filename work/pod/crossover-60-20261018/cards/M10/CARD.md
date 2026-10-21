# M10: Parker square: nine distinct squares in a magic grid

**NOT REVIEWED — inventory card only.**

Question: Can a 3-by-3 array of nine distinct positive integer squares have equal row, column and both diagonal sums?

Prior work (surveyed): Prior work screened the construction and exact-certificate fit, not a solver. No local witness or impossibility result exists; current problem status must be refreshed before asserting novelty.

Obstacle: Easy exact verification masks hard discovery; arbitrary bounded search gives no global negative result.

Candidate crossover: Use formation-control symmetry reduction: eliminate linear magic constraints first, then treat remaining square conditions as a minimal distance-geometry compatibility problem.

Proposed cheap test: Derive the standard affine magic-square parametrization independently, check it exactly, and map square constraints to a low-dimensional modular sieve with a nondegeneracy test.

Selection reason: Distinct math question with source-linked obstacle and small test; wildcard transfer reserved for exploration. Subjective rubric, not success probability.

Sources:

- /Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/prize-problems/nonerdos-finite-certificate-review.txt
