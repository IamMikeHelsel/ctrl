# Task Assignment: Byers-Nash mf13 Lean 4 Extraction Specialist (worker_mf13_extraction)

## Objective
Close the final extraction lemma in `/Users/mike/dev/ctrl/lean/Research/SkewRankFourNormalForm.lean` to deliver the final hypothesis-free theorem:
`theorem skew_rank_le_four_normal_form (K : Mat) (hK : K.transpose = -K) (hrank : K.rank ≤ 4) : ∃ (Q : Mat) (a b : ℝ), Q.transpose * Q = 1 ∧ K = conjugate Q (skewWitness a b)`
and compose with same-square exclusion.

## Working Directory
`/Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_extraction`

## Exclusive Write Ownership
- `/Users/mike/dev/ctrl/lean/Research/SkewRankFourNormalForm.lean`
- `/Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_extraction/`

## Parent Guidance & Concrete Strategy (2026-10-19T08:25:16Z)
1. Work with K as a linear map on `E6 := EuclideanSpace ℝ (Fin 6)` (`Matrix.toEuclideanLin K`).
2. Let `N := LinearMap.ker` of it, get `2 ≤ finrank ℝ N` from `ker_dim_ge_two` (transfer via linear equiv `WithLp.linearEquiv` / `EuclideanSpace.equiv` if needed).
3. Then `stdOrthonormalBasis ℝ N` (Mathlib, `Analysis.InnerProductSpace.PiL2`) indexed by `Fin (finrank ℝ N)`; take entries 0 and 1 (via `Fin.castLE` / the `≥ 2` bound) and coerce with `Submodule.subtype` — orthonormality is preserved (`Orthonormal.comp` / `Submodule.coe_inner`).
4. Confirm explicitly and complete Step 4b ($K$ acts on $\operatorname{span}(u_2, w)$ as $\beta \cdot J$: $K u_2 = \beta w$, $K w = -\beta u_2$) and Step 5 (sign/order matching $hq0..hq5$ convention).
5. Compile with `cd /Users/mike/dev/ctrl/lean && lake env lean Research/SkewRankFourNormalForm.lean`. Must have exit code 0, 0 sorry, standard axioms only (`[propext, Classical.choice, Quot.sound]`).

If any step blocks, report PRECISELY which lemma remains unproved in `handoff.md`.
Deliver complete handoff to `/Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_extraction/handoff.md`.
When complete, notify caller via `send_message`.

## 2026-10-19T08:25:58Z
Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md and /Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_extraction/DISPATCH.md before doing anything else.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_extraction.
Write only to your working directory and your exclusively owned target file:
`/Users/mike/dev/ctrl/lean/Research/SkewRankFourNormalForm.lean`.
Update progress.md regularly with timestamped progress.

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All proofs must be genuine mathematical proofs in Lean 4. DO NOT hardcode proofs, use custom axioms, or leave `sorry`. A teamwork_preview_auditor will independently verify your work.

Your mission:
Execute the parent guidance (2026-10-19T08:25:16Z) in parallel with M6:
Close the final extraction lemma in `SkewRankFourNormalForm.lean` to deliver:
`theorem skew_rank_le_four_normal_form (K : Mat) (hK : K.transpose = -K) (hrank : K.rank ≤ 4) : ∃ (Q : Mat) (a b : ℝ), Q.transpose * Q = 1 ∧ K = conjugate Q (skewWitness a b)`
with NO basis hypotheses.
