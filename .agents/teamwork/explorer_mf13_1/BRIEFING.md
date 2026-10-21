# BRIEFING — 2026-10-19T07:12:00Z

## Mission
Deeply investigate work/pod/mf13 (Byers–Nash conjecture on real 6x6 matrices), analyzing the math, reduction, numerics, Lean gap, and rational SDP / SOS certification pathway to produce a concrete attack blueprint.

## 🔒 My Identity
- Archetype: explorer
- Roles: math/control investigation, formalization analysis, certificate synthesis
- Working directory: /Users/mike/dev/ctrl/.agents/teamwork/explorer_mf13_1
- Original parent: 0b6a5e14-8c10-4497-8beb-fd637698bacb
- Milestone: Byers–Nash n=6 investigation (mf13)

## 🔒 Key Constraints
- Read-only investigation — do NOT implement
- Write only to working directory (/Users/mike/dev/ctrl/.agents/teamwork/explorer_mf13_1)
- No modification of challenge statements or files outside working directory
- Hypotheses audit discipline: distinguish genuinely proved theorems from assumed cruxes / scaffolding

## Current Parent
- Conversation ID: 0b6a5e14-8c10-4497-8beb-fd637698bacb
- Updated: 2026-10-19T06:55:14Z

## Investigation State
- **Explored paths**:
  - `work/pod/mf13/FINDINGS.md`
  - `work/pod/mf13/theory/REDUCED_SEARCH.md`
  - `work/pod/mf13/theory/NOTES.md`
  - `work/pod/mf13/theory/SameSquareExclusion.lean`
  - `work/pod/mf13/opt/NOTES.md`
  - `work/pod/mf13/bilevel/NOTES.md`
  - `work/pod/crossover-60-20261018/cards/M05/CARD.md`
  - `tools/sdp_rational_cert.py`
  - `tools/push_sdp_cert.py`
- **Key findings**:
  1. Byers–Nash $n=6$ open problem reduced to 11 outer parameters for singular pairs $(K,Y)$ plus a 9D convex inner problem for $A(z)$.
  2. Numerics (>110k evaluations) show $\min \phi(K,Y) = 1.00000000000000$, attained on two equality sets: rank-4 ridge ($\sigma_3(K) \to 0$) and full-rank Common-T locus (codim 3, dim 8).
  3. Proved Common-Involution Lemma: if $TK = -KT, TY = -YT$, then $X_v=KT, X_u=YT$ are symmetric and force $s(A) \ge k(A)$ unconditionally.
  4. Stated Lean gap identified: `SameSquareExclusion.lean` has 21 theorems zero-sorry, but requires $K = Q \cdot \text{skewWitness}(a,b) \cdot Q^T$ as input; missing skew normal form for rank $\le 4$.
  5. Rational certificate pathway: `sdp_rational_cert.py` certifies interior rational pairs with positive margin; equality sets deflated via algebraic identities.
- **Unexplored areas**: None for explorer scope; full findings delivered in `handoff.md`.

## Key Decisions Made
- Fully formulated answers to all 5 prompt questions with exact citations, line numbers, and formulas.
- Synthesized a concrete two-track blueprint (Track A for Lean normal-form formalization, Track B for rational SDP tool implementation).

## Artifact Index
- `/Users/mike/dev/ctrl/.agents/teamwork/explorer_mf13_1/progress.md` — Liveness heartbeat
- `/Users/mike/dev/ctrl/.agents/teamwork/explorer_mf13_1/BRIEFING.md` — Persistent working memory
- `/Users/mike/dev/ctrl/.agents/teamwork/explorer_mf13_1/handoff.md` — Comprehensive deliverable handoff report
