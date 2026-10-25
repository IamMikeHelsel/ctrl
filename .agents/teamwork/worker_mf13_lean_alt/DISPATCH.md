# Task Assignment: Byers-Nash mf13 Lean 4 Specialist (Alternative / Inductive Strategy)

## Objective
Formalize the rank ≤ 4 real skew 6x6 normal-form lemma in Lean 4:
`theorem skew_rank_le_four_normal_form (K : Mat) (hK : K.transpose = -K) (hrank : K.rank ≤ 4) : ∃ (Q : Mat) (a b : ℝ), Q.transpose * Q = 1 ∧ K = conjugate Q (skewWitness a b)`
with NO basis hypotheses, and compose it with the same-square comparator to close the open gap in `work/pod/mf13/theory/SameSquareExclusion.lean`.

## Working Directory
`/Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_lean_alt`

## Exclusive Write Ownership
- `/Users/mike/dev/ctrl/lean/Research/SkewRankFourNormalForm.lean`
- `/Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_lean_alt/`
Do NOT edit `Research/SkewNormalForm.lean` (owned by worker_mf13_lean).

## Context & Parent Audit Directives
Read:
- `/Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md`
- `/Users/mike/dev/ctrl/lean/Research/SkewNormalForm.lean` (for existing proven lemmas: `skew_invariant_plane`, `skew_orthogonal_plane_invariant`, `orthonormal_basis_gives_skewWitness`, `same_square`, `gain_comparison`)
- `/Users/mike/dev/ctrl/work/pod/mf13/theory/SameSquareExclusion.lean`
- Parent Audit (2026-10-19T07:49:31Z):
  "The stated gap is still open: there is NO theorem with a rank hypothesis, i.e. nothing of the form `∀ K : Mat, Kᵀ = -K → K.rank ≤ 4 → ∃ Q a b, Qᵀ*Q = 1 ∧ K = conjugate Q (skewWitness a b)`. Either deliver that exact theorem (spectral theorem on the symmetric PSD −K·K via Matrix.IsHermitian.eigenvectorBasis, pairing via skew_invariant_plane, kernel dimension ≥ 2 from rank ≤ 4 — the delicate part is choosing a K-adapted orthonormal basis when eigenvalues repeat; handle by working with eigenspaces of −K² and applying skew_invariant_plane inductively on orthogonal complements), plus the corollary composing it with the exclusion theorem for arbitrary skew K of rank ≤ 4; or report precisely what remains unproved."

## Verification
- `cd /Users/mike/dev/ctrl/lean && lake env lean Research/SkewRankFourNormalForm.lean`
- Must compile with exit code 0, 0 sorry, and standard axioms ONLY (`[propext, Classical.choice, Quot.sound]`).
- Write complete handoff report to `/Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_lean_alt/handoff.md`.
- When done, send message to caller (`0b6a5e14-8c10-4497-8beb-fd637698bacb`).


## 2026-10-19T07:50:28Z
Read /Users/mike/dev/ctrl/.agents/teamwork/ORIGINAL_REQUEST.md and /Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_lean_alt/DISPATCH.md before doing anything else.
Your working directory is /Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_lean_alt.
Write only to your working directory and your exclusively owned source file:
`/Users/mike/dev/ctrl/lean/Research/SkewRankFourNormalForm.lean`.
Update progress.md regularly with timestamped progress.

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All proofs must be genuine mathematical proofs in Lean 4. DO NOT hardcode proofs, use custom axioms, or leave `sorry`. A teamwork_preview_auditor will independently verify your work.

MANDATORY HYPOTHESIS AUDIT RULE:
The theorem MUST have NO basis hypotheses!
The stated goal from the parent audit (2026-10-19T07:49:31Z):
Deliver the exact normal form theorem with a genuine rank hypothesis:
`theorem skew_rank_le_four_normal_form (K : Mat) (hK : K.transpose = -K) (hrank : K.rank ≤ 4) : ∃ (Q : Mat) (a b : ℝ), Q.transpose * Q = 1 ∧ K = conjugate Q (skewWitness a b)`
and compose it with the same-square comparator:
`theorem general_rank_four_exclusion (K : Mat) (hK : K.transpose = -K) (hrank : K.rank ≤ 4) (A : Mat) : ∃ S : Mat, S.transpose = S ∧ frobeniusSquared S = frobeniusSquared K ∧ frobeniusSquared (lyapunov A K) ≤ frobeniusSquared (lyapunov A S)`
If fully closing the basis existence proof in Lean 4 is obstructed, report PRECISELY and rigorously what steps are proved and what remains unproved.

Verification:
- `cd /Users/mike/dev/ctrl/lean && lake env lean Research/SkewRankFourNormalForm.lean` (exit code 0, 0 sorry, standard axioms only).
Deliver your complete handoff report to /Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_lean_alt/handoff.md.
When complete, notify caller via send_message.


## 2026-10-19T08:05:45Z
**Context**: Byers-Nash mf13 normal form Lean formalization in `SkewRankFourNormalForm.lean`.
**Content**: We have observed your proven lemmas including `test_extension` (orthonormal basis extension via Mathlib's `exists_orthonormalBasis_extension_of_card_eq`) and kernel dimension rank-nullity bound. If the full unconditioned end-to-end composition without basis hypotheses is obstructed by Mathlib's `EuclideanSpace`/`WithLp` subtype coercion layer, please adhere to the parent directive: ensure all compiled code in `SkewRankFourNormalForm.lean` has 0 `sorry`, document precisely and rigorously what has been proved and what remains unproved in your `handoff.md`, and complete your report.
**Action**: Finalize `SkewRankFourNormalForm.lean` with 0 sorry, write your `handoff.md`, and send a completion message back.


## 2026-10-19T08:10:28Z
**Context**: Byers-Nash mf13 normal form Lean formalization in `SkewRankFourNormalForm.lean`.
**Content**: Parent check and constructive proof plan for `SkewRankFourNormalForm.lean`:
"The main theorem `skew_rank_le_four_normal_form` is still ABSENT. `general_rank_four_exclusion_of_normal_form` takes `h_nf : ∃ Q a b, … K = conjugate Q (skewWitness a b)` as a hypothesis — that hypothesis IS the gap. `ker_dim_ge_two` and `orthonormal_extension_pair` are genuine but auxiliary. Please don't hand off as done.

A proof plan that sidesteps the repeated-eigenvalue problem (only ONE eigenvector needed):
1. K = 0: take Q = 1, a = b = 0.
2. K ≠ 0: −K·K is Hermitian PSD (isHermitian_neg_sq) with trace ‖K‖_F² > 0, so some vector of its eigenvectorBasis has eigenvalue λ₁ > 0. Normalize to u₁; set v₁ := K u₁/√λ₁. skew_invariant_plane gives orthonormal u₁,v₁ with K u₁ = √λ₁ v₁, K v₁ = −√λ₁ u₁.
3. ker K has dim ≥ 2 (ker_dim_ge_two). u₁, v₁ ∈ range K (u₁ = −K v₁/√λ₁), and range K ⊥ ker K for skew K. So pick orthonormal z₁, z₂ ∈ ker K; they are automatically ⊥ u₁, v₁.
4. Extend (u₁,v₁,z₁,z₂) to an orthonormal basis (generalize orthonormal_extension_pair to 4 vectors); call the two new vectors u₂, w. W = span(u₂,w) = span(u₁,v₁,z₁,z₂)^⊥ is K-invariant (skew_orthogonal_plane_invariant / ker invariance). K u₂ ∈ W and u₂·K u₂ = 0 (skew), so K u₂ = β w for β = w·K u₂; by skewness K w = −β u₂. No eigen-decomposition needed for the second block.
5. Order/sign-adjust to match the hq0..hq5 convention (K q0 = −a q1, etc.: e.g. q0 = v₁, q1 = u₁ with a = √λ₁ — check signs), then apply skew_rank_four_normal_form_of_adapted_basis / orthonormal_basis_gives_skewWitness.
6. Compose with general_rank_four_exclusion_of_normal_form to get the hypothesis-free corollary for every skew K with rank ≤ 4.

If any step blocks, report exactly which lemma."

**Action**: Execute this 6-step proof plan directly in `SkewRankFourNormalForm.lean`. If any step blocks, report exactly which lemma blocks.
