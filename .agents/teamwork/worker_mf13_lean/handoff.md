# Handoff Report — Byers-Nash mf13 Lean 4 Worker

## 1. Observation
- Target Formalization File: `/Users/mike/dev/ctrl/lean/Research/SkewNormalForm.lean` (612 lines).
- Verification Python Test Suite: `/Users/mike/dev/ctrl/tests/test_skew_normal_form.py`.
- Lake environment: Lean 4.33.1 with Mathlib.
- Compilation verification command:
  ```bash
  cd /Users/mike/dev/ctrl/lean && lake env lean Research/SkewNormalForm.lean
  ```
  Result: exited with code 0, 0 errors, 0 warnings, 0 `sorry`.
  Verbatim output:
  ```text
  'Research.SkewNormalForm.skew_invariant_plane' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Research.SkewNormalForm.skew_orthogonal_plane_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Research.SkewNormalForm.skew_orthogonal_ker_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Research.SkewNormalForm.orthonormal_basis_gives_skewWitness' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Research.SkewNormalForm.rank_four_same_square_exclusion_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Research.SkewNormalForm.rank_four_conjugated_exclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
- Python test execution:
  ```bash
  uv run pytest tests/test_skew_normal_form.py
  ```
  Result: 3 passed in 0.04s (zero third-party dependencies, pure Python standard library `math` and `fractions.Fraction`).

## 2. Logic Chain
1. **Section 1 (Operators and Invariance):**
   - Verified that `conjugate Q X = Q * X * Qᵀ` preserves transposition (`conjugate_transpose`), symmetry (`conjugate_symmetric`), Frobenius norm under orthogonal $Q$ (`frobeniusSquared_conjugate`), and intertwines the Lyapunov operator $\mathcal{L}_A(X) = A X + X A^\top$ (`lyapunov_conjugate`, `lyapunov_frobeniusSquared_conjugate`).
   - Proved that `symmetricWitness a b` satisfies $S^2 = -K^2$ (`same_square`) and $\|S\|_F^2 = \|K\|_F^2$ (`same_squaredNorm`) relative to `skewWitness a b`.
2. **Section 2 (Step A.1 — 2D Invariant Subspace Lemma):**
   - Proved `dotProduct_mulVec_comm`, `skew_dotProduct_mulVec_swap`, and `skew_dotProduct_self_zero` ($u \cdot (M u) = 0$).
   - Proved `skew_invariant_plane`: for any real skew $M$ ($M^\top = -M$), $-M^2$ is symmetric PSD. Given a unit eigenvector $u$ with $(-M^2) u = \lambda u$ and $\lambda > 0$, $v = \frac{1}{\sqrt{\lambda}} M u$ satisfies:
     - $u \cdot v = 0$ and $v \cdot v = 1$ (orthonormal pair)
     - $M u = \sqrt{\lambda} v$ and $M v = -\sqrt{\lambda} u$ (acts as rotation $\sqrt{\lambda} J$)
     - $(-M^2) v = \lambda v$ (shares identical eigenvalue)
     - The 2D plane $\operatorname{span}(u, v)$ is strictly $M$-invariant.
3. **Section 3 (Step A.2 — Orthogonal Invariant Complement):**
   - Proved `skew_orthogonal_plane_invariant`: for any $w \perp u, v$, $M w \perp u, v$.
   - Proved `skew_orthogonal_ker_invariant`: for any $z \in \ker M$ and $w \perp z$, $M w \perp z$.
4. **Section 4 (Step A.4 — Orthonormal Basis to Normal Form):**
   - Defined `basisMatrix q` as the matrix with column vectors $q_j$.
   - Proved `basisMatrix_transpose_mul_self`: if $(q_0, \dots, q_5)$ is orthonormal, $Q^\top Q = 1$.
   - Proved `orthonormal_basis_gives_skewWitness`: 36-case exhaustive algebraic reduction showing that any orthonormal basis satisfying $K q_0 = -a q_1, K q_1 = a q_0, K q_2 = -b q_3, K q_3 = b q_2, K q_4 = 0, K q_5 = 0$ yields $Q^\top K Q = \operatorname{skewWitness}(a, b)$ and $K = \operatorname{conjugate} Q (\operatorname{skewWitness}(a, b))$.
5. **Section 5 (Unconditional Signed SVD and Conjugated Comparison):**
   - Proved `gain_difference` and `gain_comparison`: active off-diagonal block diagonalized implies $E_A(S) \ge E_A(K)$.
   - Proved `unit_normal_exists`, `half_angle_exists`, and `signed_svd_angles_exist`: unconditional existence of $SO(2) \times SO(2)$ rotation angles diagonalizing the off-diagonal $2 \times 2$ block of $A$.
   - Proved `blockRot6_orthogonal` and `blockRot6_preserves_skewWitness`.
   - Proved `rank_four_same_square_exclusion_unconditional` and `rank_four_conjugated_exclusion`: for any matrix of the form $K = \operatorname{conjugate} Q (\operatorname{skewWitness}(a, b))$, there exists symmetric same-square $S$ with $E_A(K) \le E_A(S)$.

## 3. Caveats & Precise Stated Gap Audit
- **What is 100% Proved (Zero sorry, standard axioms only):**
  - All invariant subspace and complement lemmas.
  - The theorem `orthonormal_basis_gives_skewWitness` which proves that the existence of an adapted orthonormal basis implies the orthogonal normal form.
  - Unconditional rank-4 exclusion for all conjugated witnesses $Q \cdot \operatorname{skewWitness}(a, b) \cdot Q^\top$.
- **What Remains Unproved (The Core Stated Gap):**
  - The unconditional existence lemma without basis hypotheses:
    ```lean
    theorem skew_rank_le_four_normal_form (K : Mat) (hK : K.transpose = -K) (hrank : K.rank ≤ 4) :
        ∃ (Q : Mat) (a b : ℝ), Q.transpose * Q = 1 ∧ K = conjugate Q (skewWitness a b)
    ```
  - **Exact Technical Obstacle:**
    Mathlib's spectral theorem (`Matrix.IsHermitian.eigenvectorBasis`) provides an orthonormal eigenbasis for $-K^2$, but when eigenvalues repeat (multiplicity 4 for $a = b > 0$, or repeated 0 in the kernel), the basis returned by Mathlib is an arbitrary orthonormal basis of the eigenspace. Aligning it with $K$ requires formalizing an internal orthogonal rotation within each eigenspace by applying `skew_invariant_plane` inductively to orthogonal complements, and extracting an orthonormal pair from $\ker(K)$ (whose dimension is $\ge 2$ via rank-nullity). Mathlib lacks a pre-packaged skew-normal-form or real Schur decomposition, so this induction requires substantial submodule and subtype formalization.
  - Per the Parent Audit Directive (2026-10-19T07:49:31Z), we do NOT claim that this gap is closed, nor do we smuggle the hypothesis. We report the exact boundaries honestly.

## 4. Conclusion
1. All core building blocks (`skew_invariant_plane`, `skew_orthogonal_plane_invariant`, `skew_orthogonal_ker_invariant`, `orthonormal_basis_gives_skewWitness`, `rank_four_conjugated_exclusion`) are fully formalized and verified in `lean/Research/SkewNormalForm.lean` with exit code 0, 0 warnings, 0 `sorry`, and only standard axioms `[propext, Classical.choice, Quot.sound]`.
2. The Python verification suite `tests/test_skew_normal_form.py` is pure standard library and passes 100%.
3. The exact mathematical boundary between the proved reduction theorem and the open eigenspace-alignment existence lemma has been rigorously audited and documented.

## 5. Verification Method
1. Compile Lean 4 formalization:
   ```bash
   cd /Users/mike/dev/ctrl/lean && lake env lean Research/SkewNormalForm.lean
   ```
   *Expected:* Exit code 0, no errors, no warnings, `#print axioms` outputs showing only `[propext, Classical.choice, Quot.sound]`.
2. Run pure Python test suite:
   ```bash
   uv run pytest tests/test_skew_normal_form.py
   ```
   *Expected:* 3 passed in < 0.1s.
3. Invalidation condition: Any presence of `sorry`, custom axioms, or compilation failures.
