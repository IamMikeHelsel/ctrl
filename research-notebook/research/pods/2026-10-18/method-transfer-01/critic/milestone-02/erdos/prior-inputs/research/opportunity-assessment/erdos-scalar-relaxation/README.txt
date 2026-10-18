What the completed Erdős bridge does and does not open up
17 October 2026

The current cut/completion proof is close to the limit of its scalar relaxation.
The standard-library exact-rational diagnostic probe.py supplies a feasible
point satisfying every inequality consumed by CutScalar.cut_scalar_bound,
including the graph-wrapper orientation/normalization constraints, with

    beta = 6256019367 / 241832986336 = approximately 0.0258691730263.

Thus those scalar inequalities alone cannot imply beta <= 0.02586. More precise
rounding of the current 0.02587 certificate cannot get to that target, much less
the conjectural0.02. There may be a smaller improvement above this obstruction;
this diagnostic does not determine the optimal scalar constant.

The feasible point is a point of a relaxation. We do NOT assert that a graph
realizes its edge densities. It is not a counterexample to the graph conjecture
or a lower bound on the true optimal graph constant. Graph-realizability
constraints are precisely one possible source of a stronger future inequality.

The next mathematical search should target another graph construction, an
inequality linking the cut densities to the completion profile, or a stronger
max-cut input. Keep this separate from formalizing BCL itself: formalizing a
published input would close a foundational dependency without improving the
numerical bound.

Reproduce: python3 probe.py
The saved output is diagnostic.json. Fraction arithmetic is exact; all checks
are assertions. This small diagnostic has not been formalized in Lean and makes
no novelty claim. Source hashes identify the frozen scalar hypotheses inspected.
