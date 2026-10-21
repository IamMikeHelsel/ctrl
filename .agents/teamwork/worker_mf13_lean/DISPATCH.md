# Task Assignment: Byers-Nash mf13 Lean 4 Worker

## Objective
Formalize the rank ≤ 4 real skew 6x6 normal-form lemma in Lean 4, discharging the stated open gap in `work/pod/mf13/theory/SameSquareExclusion.lean`.

## Working Directory
`/Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_lean`

## Mandatory Integrity Warning
DO NOT CHEAT. All implementations must be genuine mathematical proofs. DO NOT hardcode proofs, use axioms beyond standard `[propext, Classical.choice, Quot.sound]`, or leave `sorry`. A teamwork_preview_auditor will independently verify your work.

## Mandatory Hypothesis Audit Rule
Every theorem must have zero smuggled cruxes. List all hypotheses and structure fields.

## Detailed Scope
1. Exclusive write ownership:
   - `/Users/mike/dev/ctrl/lean/Research/SkewNormalForm.lean`
   - `/Users/mike/dev/ctrl/tests/test_skew_normal_form.py` (if python tests needed)
2. Mathematical Target:
   In `lean/Research/SkewNormalForm.lean`:
   - Follow the Step-by-Step Blueprint from `/Users/mike/dev/ctrl/.agents/teamwork/explorer_mf13_1/handoff.md` Section 5:
     (a) 2D Invariant Subspace Lemma: for any real skew matrix $M$ ($M^\top = -M$), $-M^2$ is symmetric positive semidefinite; extracting an eigenvector $u$ with eigenvalue $\lambda \ge 0$ and $v = \frac{1}{\sqrt{\lambda}} M u$ spans a 2D $M$-invariant subspace where $M$ acts as $\sqrt{\lambda} J$.
     (b) Orthogonal Invariant Complement: if $V$ is $M$-invariant, then $V^\perp$ is $M$-invariant.
     (c) Rank ≤ 4 Normal Form for $6 \times 6$: For any real skew $K \in \mathbb{R}^{6 \times 6}$ with rank ≤ 4, there exists an orthogonal matrix $Q \in O(6)$ and $a, b \in \mathbb{R}$ such that $Q^\top K Q$ has the 2x2 block diagonal form $\operatorname{diag}(aJ, bJ, 0_{2 \times 2})$.
     (d) Connect with the same-square comparator: prove that for any such $K$ and any $A \in \mathbb{R}^{6 \times 6}$, there exists a symmetric $S \in \mathbb{S}_6$ with $\|S\|_F^2 = \|K\|_F^2$ and $\|\mathcal{L}_A(S)\|_F^2 \ge \|\mathcal{L}_A(K)\|_F^2$.
3. Verification:
   - Build cleanly with `cd /Users/mike/dev/ctrl/lean && lake env lean Research/SkewNormalForm.lean`.
   - Exit code 0, 0 `sorry`, standard axioms ONLY (`[propext, Classical.choice, Quot.sound]`).
4. Deliver your complete handoff report to `/Users/mike/dev/ctrl/.agents/teamwork/worker_mf13_lean/handoff.md`.
When done, notify caller via `send_message`.

## 2026-10-19T07:21:17Z
Caller update regarding tests/test_skew_normal_form.py:
numpy is not an installed dependency in root python environment.
Use pure Python standard library (math, fractions, nested lists) so that `uv run pytest` passes cleanly.

## 2026-10-19T07:34:35Z
Sender: 0b6a5e14-8c10-4497-8beb-fd637698bacb
Context: Byers–Nash (mf13) Lean 4 Normal Form Lemma (`lean/Research/SkewNormalForm.lean`).
Content: Parent audit directive:
The building blocks you proved (`skew_invariant_plane`, `skew_orthogonal_plane_invariant`, `orthonormal_basis_gives_skewWitness`) are genuine mathematical content. But `orthonormal_basis_gives_skewWitness` currently takes the adapted orthonormal basis and its K-action as hypotheses — the existence of that basis (the actual normal-form lemma) must be closed!
To close it:
- `-K * K` is symmetric PSD, so Mathlib's `Matrix.IsHermitian.eigenvectorBasis` / `Matrix.IsHermitian.spectral_theorem` gives an orthonormal eigenbasis.
- Pair eigenvectors via `skew_invariant_plane`, and use `K.rank ≤ 4` (or kernel dimension ≥ 2) to get the zero block.
- Deliver the theorem with NO basis hypotheses:
  `theorem skew_rank_le_four_normal_form (K : Mat) (hK : K.transpose = -K) (hrank : K.rank ≤ 4) : ∃ (Q : Mat) (a b : ℝ), Q.transpose * Q = 1 ∧ K = conjugate Q (skewWitness a b)`
- Then plug this directly into `SameSquareExclusion` to close the open gap.
Action: Implement and compile this theorem without basis hypotheses, verify with `#print axioms` (0 sorry, standard axioms only), and report in `handoff.md`.

## 2026-10-19T07:50:12Z
Sender: 0b6a5e14-8c10-4497-8beb-fd637698bacb
Context: Byers–Nash (mf13) Lean 4 Normal Form Lemma (`lean/Research/SkewNormalForm.lean`).
Content: Urgent parent audit (2026-10-19T07:49:31Z):
"The new theorems `rank_four_same_square_exclusion_unconditional` and `rank_four_conjugated_exclusion` take K already in the form Q·skewWitness(a,b)·Qᵀ. That is exactly what work/pod/mf13/theory/SameSquareExclusion.lean ALREADY proved (FINDINGS M3: 'unconditional rank-2 and rank-4 same-square exclusion in Fin 6 for witnesses Q·skewWitness(a,b)·Qᵀ'). So this is a re-proof, not progress. The stated gap is still open: there is NO theorem in the file with a rank hypothesis, i.e. nothing of the form `∀ K : Mat, Kᵀ = -K → K.rank ≤ 4 → ∃ Q a b, Qᵀ*Q = 1 ∧ K = conjugate Q (skewWitness a b)`.

Please do not move to M6 claiming the normal-form gap is closed. Either deliver that exact theorem (spectral theorem on the symmetric PSD −K·K via Matrix.IsHermitian.eigenvectorBasis, pairing via skew_invariant_plane, kernel dimension ≥ 2 from rank ≤ 4 — the delicate part is choosing a K-adapted orthonormal basis when eigenvalues repeat; handle by working with eigenspaces of −K² and applying skew_invariant_plane inductively on orthogonal complements), plus the corollary composing it with the exclusion theorem for arbitrary skew K of rank ≤ 4; or report precisely what remains unproved. This is worth one focused push before M6."
Action: Implement `theorem skew_rank_le_four_normal_form (K : Mat) (hK : K.transpose = -K) (hrank : K.rank ≤ 4) : ∃ (Q : Mat) (a b : ℝ), Q.transpose * Q = 1 ∧ K = conjugate Q (skewWitness a b)` with 0 sorry and standard axioms, or report precisely what remains unproved in `handoff.md`.
