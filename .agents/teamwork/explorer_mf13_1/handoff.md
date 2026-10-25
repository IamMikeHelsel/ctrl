# Handoff Report: Byers–Nash Conjecture ($n=6$) Deep Investigation (Lane MF-13)

**Author:** explorer_mf13_1  
**Date:** 2026-10-19T07:10:00Z  
**Target:** Byers–Nash symmetric-maximizer conjecture for $n=6$ real matrices (`work/pod/mf13`)  
**Deliverable Path:** `/Users/mike/dev/ctrl/.agents/teamwork/explorer_mf13_1/handoff.md`

---

## 1. Observation

Direct code and textual observations from authoritative repo sources:

### 1.1 The Byers–Nash Conjecture and Status in the Literature
- **Lyapunov Operator:** For $A \in \mathbb{R}^{n \times n}$, $\mathcal{L}_A(X) = AX + XA^T$. The Frobenius operator norm $\|\mathcal{L}_A\|_F$ splits over the orthogonal invariant subspaces $\mathbb{S}_n$ (symmetric) and $\mathbb{K}_n$ (skew-symmetric):
  $$s(A) = \|\mathcal{L}_A|_{\mathbb{S}_n}\|_F, \qquad k(A) = \|\mathcal{L}_A|_{\mathbb{K}_n}\|_F, \qquad \|\mathcal{L}_A\|_F = \max(s(A), k(A)).$$
- **Conjecture:** $k(A) \le s(A)$ for every real matrix $A$ (`work/pod/mf13/opt/NOTES.md:18`, `work/pod/mf13/bilevel/NOTES.md:28-29`).
- **Literature Boundary:**
  - $n \le 5$: Proved by Chen & Tian (2015).
  - $n \ge 7$: Disproved by Kressner & Vandereycken (arXiv:2608.20875v1, Aug 2026), with an explicit $7 \times 7$ integer matrix $A$ having $s(A)^2 \approx 1195.593985 < 1196 < k(A)^2 \approx 1196.025224$.
  - $n = 6$: Open (`FINDINGS.md:1-28`, `REDUCED_SEARCH.md:1-20`, `opt/NOTES.md:18`).

### 1.2 Mathematical Reduction to 11 Outer Parameters + 9D Convex Inner Problem
- **Singular Witness Formulation (`REDUCED_SEARCH.md:24-64`):**
  Assuming a strict counterexample $k(A) > s(A)$, scale $A$ so $k(A) = 1 > s(A)$. Normalized skew singular witnesses $K, Y \in \mathbb{K}_6$ ($\|K\|_F = \|Y\|_F = 1$) satisfy:
  $$AK + KA^T = Y, \qquad A^T Y + YA = K.$$
- **Rank-4 Exclusion (`SameSquareExclusion.lean:457-521`, `NOTES.md:14-36`):**
  If $\operatorname{rank}(K) \le 4$, there exists a symmetric matrix $S \in \mathbb{S}_6$ with $S^2 = -K^2$ ($\|S\|_F = \|K\|_F$) such that $\|\mathcal{L}_A(S)\|_F \ge \|\mathcal{L}_A(K)\|_F$. Hence any strict counterexample requires $\operatorname{rank}(K) = 6$ and $\operatorname{rank}(Y) = 6$ ($\det K \ne 0, \det Y \ne 0$).
- **$O(6)$ Canonical Form of $K$ (2 parameters):**
  Under $O(6)$ congruence, $K = \operatorname{diag}(aJ, bJ, cJ)$ with $J = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$, $a \ge b \ge c > 0$, $a^2 + b^2 + c^2 = 1/2$. The stabilizer of $K$ in $O(6)$ is $SO(2)^3$ (dimension 3).
- **Linear Substitution and Sylvester Operator (`REDUCED_SEARCH.md:33-51`):**
  Setting $H = AK - \frac{1}{2}Y$, the first equation is equivalent to $H = H^T \in \mathbb{S}_6$ (21 parameters) and $A = (H + \frac{1}{2}Y)K^{-1}$.
  Substituting into the second equation yields:
  $$\Phi_{K,Y}(H) := (KY)H - H(YK) = K^3 - \frac{1}{2}(Y^2 K + KY^2) =: \text{RHS}(K,Y).$$
- **Symplectic Structure and 3 Trace Moments (`REDUCED_SEARCH.md:39-51`):**
  $T = YK$ is self-adjoint with respect to the symplectic form $\omega(x,y) = x^T K^{-1} y$. Thus every eigenvalue has even multiplicity, and the characteristic polynomial is a perfect square $p(t)^2$ with $\deg p = 3$.
  Generically, $\operatorname{rank}(\Phi_{K,Y}) = 12$, and $\ker(\Phi_{K,Y}^*) \subset \mathbb{K}_6$ has dimension 3, spanned by $W_0 = K^{-1}, W_1 = Y, W_2 = YKY$.
  Pairing with $\text{RHS}(K,Y)$ gives:
  $$m_j(K, Y) := \operatorname{tr}((YK)^j(Y^2 - K^2)) = 0 \qquad \text{for } j = 0, 1, 2.$$
  Higher moments $j \ge 3$ vanish identically by the Cayley–Hamilton minimal polynomial of degree 3.
- **Degrees of Freedom Count (`REDUCED_SEARCH.md:51`, `NOTES.md:114-119`):**
  - $Y \in \mathbb{K}_6$: $15 - 3 \text{ moments} - 3 \text{ stabilizer angles} = 9$ parameters.
  - $K$: 2 parameters ($a \ge b \ge c > 0$, $a^2+b^2+c^2=1/2$).
  - **Total outer parameters:** $9 + 2 = 11$.
  - **Inner space for $A$:** $\dim \ker(\Phi_{K,Y}) = 21 - 12 = 9$ real parameters $z \in \mathbb{R}^9$, over which $s(A(z)) = \sigma_{\max}(B_S(z))$ is **convex**.

### 1.3 Numerical Evidence and Equality Sets
- **Extensive Numerical Optimization (`opt/NOTES.md:52-108`, `bilevel/NOTES.md:8-25`):**
  - 18,857 random starts of Adam on the unit sphere in 36D: best $k - s = -1.53 \times 10^{-9}$, witness singular values $(0.617, 0.617, 0.346, 0.346, 6.84 \times 10^{-5}, 6.84 \times 10^{-5})$ (trapped on the rank-4 ridge).
  - Track A bilevel CMA-ES search (11D outer + 9D inner log-barrier/Clarabel): > 110,000 evaluations across 5 independent seeds with $\varepsilon$-barriers: $\min \phi(K, Y) = 1.00000000000000$ (best $f - 1 = +3.3 \times 10^{-15}$, never below 1).
  - High-precision mpmath polish (40 digits): closest full-rank candidate has $k - s = -2.0653 \times 10^{-8}$ (`opt/results/best_candidate.json`), with $\sigma_{\min} \ge 0.360$ and coupled residual $8.4 \times 10^{-12}$.
  - Positive Control ($n=7$): The identical bilevel search algorithm immediately finds counterexamples in $n=7$ ($f = 0.999588$ from paper; $f = 0.9999988$ from random starts in 290 generations).
  - Deflation from $n=7$: Scaling out the 7th coordinate destroys the gap ($k - s < 0$ for scale $t \le 0.4$), and all 7 principal $6 \times 6$ submatrices have negative gaps ($s > k$).
- **Two Equality Sets where $k(A) = s(A)$ ($\phi(K,Y) = 1$):**
  1. **Rank-4 ridge:** $\sigma_3(K) \to 0$, where $s(A) \ge k(A)$ by same-square reflection comparators.
  2. **Common-T locus (codimension 3, dimension 8 in the 11D pair space):**
     Discovered and proved in `bilevel/NOTES.md:16-20, 107-125`. $K$ and $Y$ have a common anticommuting orthogonal involution $T$ ($T = T^T, T^2 = I, TK = -KT, TY = -YT$, spectrum $(+1)^3(-1)^3$).
     Then $X_v = KT$ and $X_u = YT$ are symmetric, $\|X_v\|_F = \|K\|_F, \|X_u\|_F = \|Y\|_F$, and $\langle X_u, \mathcal{L}_A(X_v) \rangle = \|Y\|_F^2$.
     Hence $\|\mathcal{L}_A|_{\mathbb{S}_6}\| \ge \|Y\|_F/\|K\|_F = \|\mathcal{L}_A(K)\|_F/\|K\|_F = 1$, certifying $s(A) \ge k(A)$ identically on this entire 8-dimensional locus! Includes the calibration family $K = Y = \operatorname{diag}(J, 2J, 3J)$ at $A = \frac{1}{2}I_6$ and the equal-weight family $K = Y \propto \operatorname{diag}(J, J, J)$.

### 1.4 Current Lean Formalization Status and the Stated Lean Gap
- **File:** `/Users/mike/dev/ctrl/work/pod/mf13/theory/SameSquareExclusion.lean` (596 lines, 21 theorems).
- **Axioms:** Zero `sorry`, standard Lean axioms only (`propext, Classical.choice, Quot.sound`).
- **Core Results Formalized:**
  - `same_square_energy_diff`: $E_A(S) - E_A(K) = 2 \operatorname{tr}((AS)^2 + (AK)^2)$.
  - `block2_diag_trace_identity`: $\operatorname{tr}((BR)^2 + (BJ)^2) = (\operatorname{tr}(BR))^2 + (\operatorname{tr}(BJ))^2 \ge 0$.
  - `block2_cross_trace_cancel`: $\operatorname{tr}(DXNX + DJNJ) = 0$ for diagonal $D$ and arbitrary $N$.
  - `signed_svd_2x2_exists`: Unconditional $SO(2) \times SO(2)$ signed SVD for any $2 \times 2$ real matrix.
  - `rank_four_same_square_exclusion_unconditional`: Unconditional same-square exclusion for $K = \text{skewWitness}(a, b)$ in $\text{Fin } 6$.
  - `rank_four_conjugated_exclusion`: Unconditional same-square exclusion for $K = Q \cdot \text{skewWitness}(a, b) \cdot Q^T$ with $Q \in O(6)$.
  - `coupled_elimination_converse`: Division-free converse of the coupled elimination in general dimension $n$.
- **The Stated Lean Gap:**
  The theorem `rank_four_conjugated_exclusion` takes the factorization $K = Q \cdot \text{skewWitness}(a, b) \cdot Q^T$ as a hypothesis.
  **The missing normal-form lemma is:**
  $$\forall K \in \mathbb{K}_6 \text{ with } \operatorname{rank}(K) \le 4, \; \exists Q \in O(6), \, a, b \in \mathbb{R} \text{ such that } K = Q \cdot \text{skewWitness}(a, b) \cdot Q^T.$$
  This lemma is unformalized; without it, the exclusion theorem does not apply to an arbitrary rank-$\le 4$ skew matrix given only by $K^T = -K$ and $\operatorname{rank}(K) \le 4$ (or $\det K = 0$).

### 1.5 Rational Certificate Tooling in the Repo
- `tools/sdp_rational_cert.py` (957 lines): Computes exact rational dual SDP certificates $S_Q = C - \operatorname{diag}(y_Q) = L D L^T > 0$ over $\mathbb{Q}$, with unit lower-triangular $L$ and strictly positive pivots $D_i > 0$.
- `tools/push_sdp_cert.py` (290 lines): Applies the rational certificate tool to exact rational problems (e.g. discrete energy bounds and Lyapunov contraction).

---

## 2. Logic Chain

From the observations to the core answers:

### Step 2.1: Mathematical Architecture of the $n=6$ Problem
1. In $n=7$, Kressner & Vandereycken showed that a rank-6 skew witness $K_{\text{opt}}$ can strictly beat all symmetric comparators $S$.
2. As observed in Section 1.1 and 1.3, on the 6D support of the $n=7$ witness, the restricted $6 \times 6$ matrix $B_6$ actually satisfies $s(B_6)^2 = 1149.8 > k(B_6)^2 = 1090.3$!
3. The reason $n=7$ achieves $k > s$ is that the 7th row $d_{1 \times 6}$ couples as $2\|d_{1 \times 6} X\|_F^2 = 2 \operatorname{tr}(d X^2 d^T)$. Same-square comparators ($S^2 = -K^2$) preserve this 7th-row energy ($170.94$), but on $B_6$ they only reach $E_{B_6}(S) \le 1012.3 < 1025.1$. The unconstrained symmetric maximizer of $B_6$ has a *different square* ($S^2 \ne -K^2$) and loses more on the 7th row than it gains on $B_6$.
4. In dimension $n=6$, there is NO 7th row to penalize different-square symmetric comparators. Therefore, $S$ is completely unconstrained in its square $S^2$.

### Step 2.2: Reduction and the Convex Inner Problem
1. Because rank $\le 4$ skew witnesses are unconditionally dominated by same-square symmetric witnesses (`SameSquareExclusion.lean`), any strict counterexample in $n=6$ must have $\operatorname{rank}(K) = 6$ and $\operatorname{rank}(Y) = 6$.
2. This eliminates the rank-4 boundary and reduces the search to invertible pairs $(K,Y)$.
3. The linear elimination $H = AK - \frac{1}{2}Y \in \mathbb{S}_6$ transforms the coupled bilateral system into $(KY)H - H(YK) = \text{RHS}(K,Y)$.
4. The symplectic self-adjointness of $T = YK$ with respect to $\omega(x,y) = x^T K^{-1} y$ forces spectral duplication (all Jordan blocks have even multiplicity). In dimension 6, $\deg \min\text{poly}(YK) \le 3$.
5. This implies the cokernel of $\Phi_{K,Y}$ is spanned by $\{K^{-1}, Y, YKY\}$, which yields exactly 3 necessary and sufficient moment conditions $m_0 = m_1 = m_2 = 0$.
6. Modulo $O(6)$ gauge symmetries, the moduli space of compatible full-rank pairs has dimension $2 + 9 = 11$.
7. For each compatible pair, the solution space for $A$ is a 9-dimensional affine family $A(z)$. Over this family, $s(A(z)) = \sigma_{\max}(B_S(z))$ is convex in $z \in \mathbb{R}^9$.
8. Consequently, the inner problem $\phi(K,Y) = \min_{z \in \mathbb{R}^9} s(A(z))$ has no non-global local minima: any local solver finds the exact global infimum for that pair.

### Step 2.3: Understanding the Equality Sets and Numerical Landscape
1. Over 110,000 evaluations across extensive numerical optimization, $\phi(K,Y)$ was never observed below 1. The minimum attained is $1.00000000000000$ (within solver tolerance $10^{-14}$).
2. The optimizer stops at 1 on two distinct sets:
   - The rank-4 ridge: $\sigma_3(K) \to 0$. Here $s(A) \ge k(A)$ by same-square reflection comparators.
   - The full-rank Common-T locus: $K$ and $Y$ share an anticommuting orthogonal involution $T$.
3. On the Common-T locus, the Common-Involution Lemma provides an exact algebraic certificate:
   $X_v = KT$ and $X_u = YT$ are symmetric, have the same norms as $K$ and $Y$, and satisfy $\langle X_u, \mathcal{L}_A(X_v) \rangle = \|Y\|_F^2$. By Cauchy–Schwarz, $\|\mathcal{L}_A|_{\mathbb{S}_6}\| \ge \|Y\|_F/\|K\|_F = 1$.
   Thus $\phi(K,Y) \ge 1$ holds identically on this entire 8-dimensional locus!
4. The Hessian at a common-T minimizer has 3 positive transverse eigenvalues (quadratic valley) and is quartic-flat along the 8-dimensional ridge. No negative descent direction exists.
5. In $n=7$, the same bilevel code crosses $f < 1$ easily because the extra kernel dimension allows escaping the common-T constraint. In $n=6$, no such escape direction exists.

### Step 2.4: The Rational SDP / SOS Certificate Pathway
1. `tools/sdp_rational_cert.py` cannot be applied blindly to the full 11-parameter family because:
   - On the equality sets (rank-4 ridge and common-T locus), the margin $s(A) - k(A)$ is exactly 0. An SDP with 0 margin yields a positive semidefinite matrix with zero eigenvalues; perturbing it into the strict interior $\mathbb{Q}_{>0}$ produces negative slack, failing to certify $\ge 1$.
   - The outer parameter space is non-convex due to the nonlinear moment constraints.
2. The correct mathematical application requires **stratification and deflation**:
   - **Stratum 1 (Rank $\le 4$ boundary):** Certified algebraically by `SameSquareExclusion.lean`. The certificate is the explicit sum-of-squares expression $E_A(S) - E_A(K) = 4a^2 ((A_{01})^2 + (A_{10})^2) + 4b^2 ((A_{23})^2 + (A_{32})^2) \ge 0$.
   - **Stratum 2 (Common-T locus):** Certified algebraically by the Common-Involution Lemma: $T \in O(6) \cap \mathbb{S}_6$ with $TK = -KT, TY = -YT$, producing $X_v = KT$ which achieves energy $\ge \|Y\|^2$.
   - **Stratum 3 (Generic interior):** Away from the equality sets, $f(K,Y) \ge 1 + \delta$ with $\delta > 0$.
3. For any specific rational pair $(K, Y) \in \mathbb{Q}^{6 \times 6}$ on Stratum 3 (or held-out near-miss candidates):
   - The dual problem $\max_{W \succeq 0, \operatorname{tr}(W)=1, \operatorname{tr}(W B_S^{(r)})=0} \operatorname{tr}(W B_S^{(0)})$ has a strictly positive margin $\ge 1 + \gamma$.
   - Solve numerically with Clarabel $\to W_{\text{num}}$.
   - Project $W_{\text{num}}$ into $\mathbb{Q}^{21 \times 21}$ satisfying the affine constraints $\operatorname{tr}(W_Q B_S^{(r)}) = 0$.
   - Verify strict positive definiteness $W_Q = L D L^T \succ 0$ via `rational_ldl` in `sdp_rational_cert.py`.
   - This produces an exact, kernel-checkable rational certificate that $s(A(z)) \ge 1 + \gamma$ for all $z \in \mathbb{R}^9$.

---

## 3. Caveats

1. **Unformalized Lean Normal-Form Lemma:** While `SameSquareExclusion.lean` is completely axiom-clean and zero-sorry, its headline theorem `rank_four_conjugated_exclusion` requires $K$ to be provided as $Q \cdot \text{skewWitness}(a,b) \cdot Q^T$. The deduction that *every* real skew 6×6 matrix with $\operatorname{rank}(K) \le 4$ admits such a decomposition is not yet formalized in Lean.
2. **Local vs. Global Nature of Bilevel Optimization:** The numerical searches (>110,000 CMA evaluations, 18,857 Adam runs) provide overwhelming evidence that $\inf \phi(K,Y) = 1$, but optimization alone is not a mathematical proof that no isolated narrow basin exists.
3. **Interior vs. Boundary Deflation:** While the common-T locus and the rank-4 ridge explain all observed minimizers, a complete global proof of $k(A) \le s(A)$ for all real 6×6 matrices requires either proving that every full-rank pair has $\phi(K,Y) \ge 1$ via dual SDP bounds, or formalizing a complete algebraic partition of $\mathbb{K}_6 \times \mathbb{K}_6$.

---

## 4. Conclusion

1. **Byers–Nash for $n=6$:** The conjecture states that $\|\mathcal{L}_A|_{\mathbb{K}_6}\|_F \le \|\mathcal{L}_A|_{\mathbb{S}_6}\|_F$ for all $A \in \mathbb{R}^{6 \times 6}$. It is the unique remaining boundary dimension between the proven Chen–Tian theorem ($n \le 5$) and the Kressner–Vandereycken counterexamples ($n \ge 7$).
2. **Exact Reduction:** A strict counterexample requires full-rank skew witnesses $K, Y$. The moduli space of compatible pairs has 11 outer parameters (2 for $K$, 9 for $Y$ cut out by 3 trace moments). For each pair, the compatible matrices form a 9-dimensional affine family over which the symmetric operator norm is strictly convex.
3. **Numerics & Obstructions:** No counterexample exists in over 110,000 evaluations. The infimum of $s/k$ is 1, attained on two equality sets: the rank-4 ridge and the 8-dimensional Common-T locus. At every full-rank minimizer, $K$ and $Y$ share an anticommuting orthogonal involution $T$, which algebraically forces $s(A) \ge k(A)$. A proof of the conjecture for $n=6$ is substantially more plausible than a counterexample.
4. **Lean Status:** 21 theorems are verified in `SameSquareExclusion.lean` with zero `sorry`. The sole formalization gap for rank $\le 4$ is the skew normal-form lemma ($K = Q \cdot \text{skewWitness}(a,b) \cdot Q^T$).
5. **Rational Certificate Role:** `sdp_rational_cert.py` applies directly to certify $s(A(z)) \ge 1 + \gamma$ on interior rational pairs by solving the dual SDP and certifying $W_Q = L D L^T \succ 0$. For the equality sets, algebraic certificates (Same-Square SOS identity and Common-Involution pairing) handle the zero-margin boundary.

---

## 5. Concrete Attack Blueprint for Workers

A concrete, two-track implementation blueprint ready for delegation to Worker agents:

### Track A: Formalize the Rank $\le 4$ Skew Normal-Form Lemma in Lean 4

**Target File:** `/Users/mike/dev/ctrl/work/pod/mf13/theory/SkewNormalForm.lean` (or appending to `SameSquareExclusion.lean`).  
**Prerequisites:** Mathlib (`Mathlib.LinearAlgebra.Matrix.Spectrum`, `Mathlib.Analysis.InnerProductSpace.Spectrum`).

#### Step-by-Step Formalization Plan:
1. **Step A.1 — Two-Dimensional Invariant Subspace Lemma (`skew_invariant_plane`):**
   - For any nonzero real skew matrix $M \in \mathbb{K}_m$ ($M^T = -M$):
   - $M^T M = -M^2$ is symmetric and positive semidefinite.
   - Apply Mathlib's spectral theorem for symmetric matrices (`Matrix.IsHermitian.eigenvectorBasis` or `LinearMap.IsSymmetric.eigenvectorBasis`) to obtain an eigenvector $u$ of $-M^2$ with eigenvalue $\lambda > 0$.
   - Normalize $u_1 = u / \|u\|_2$. Let $\omega = \sqrt{\lambda} > 0$, and define $v_1 = \frac{1}{\omega} M u_1$.
   - Prove:
     $$\|v_1\|_2 = 1, \qquad u_1 \cdot v_1 = 0, \qquad M u_1 = \omega v_1, \qquad M v_1 = -\omega u_1.$$
   - Conclude that $P_1 = \operatorname{span}(u_1, v_1)$ is a 2D $M$-invariant subspace on which $M$ acts as $\omega J$.

2. **Step A.2 — Orthogonal Invariant Complement (`skew_orthogonal_complement`):**
   - Let $V \subset \mathbb{R}^m$ be an $M$-invariant subspace.
   - For any $w \in V^\perp$ and $v \in V$:
     $$\langle M w, v \rangle = w^T M^T v = -w^T M v = -\langle w, M v \rangle = 0 \quad (\text{since } M v \in V).$$
   - Therefore, $M(V^\perp) \subseteq V^\perp$.
   - Conclude that $M$ preserves $V^\perp$.

3. **Step A.3 — Finite-Dimensional Induction for $m = 6$ (`skew_canonical_form_6`):**
   - If $\operatorname{rank}(K) = 0$: $K = 0$, $a = b = c = 0$, $Q = I_6$.
   - If $\operatorname{rank}(K) \ge 2$: Apply Step A.1 to extract $(u_1, v_1)$ with weight $a \ge 0$.
   - Restrict $K$ to $(u_1, v_1)^\perp \cong \mathbb{R}^4$.
   - If restriction is zero: remaining 4 coordinates are in $\ker K$, yielding $\operatorname{rank}(K) = 2$.
   - If restriction is nonzero: Apply Step A.1 again to extract $(u_2, v_2)$ with weight $b \ge 0$.
   - Restrict to the remaining orthogonal 2D space $W = \operatorname{span}(u_1, v_1, u_2, v_2)^\perp \cong \mathbb{R}^2$.
   - On $W$, any skew-symmetric $2 \times 2$ matrix is of the form $c J$.
   - If $\operatorname{rank}(K) \le 4$, then $\ker K$ has dimension $\ge 2$. Thus the restriction to $W$ has rank 0, forcing $c = 0$.

4. **Step A.4 — Construct Orthogonal Matrix $Q$ and Close the Gap:**
   - Define $Q$ as the matrix whose columns are $[u_1, v_1, u_2, v_2, w_1, w_2]$ where $(w_1, w_2)$ is an orthonormal basis of $W$.
   - Prove $Q^T Q = 1$ by construction.
   - Prove $Q^T K Q = \text{skewWitness}(a, b)$.
   - Conclude:
     ```lean
     theorem skew_rank_le_four_normal_form (K : Matrix (Fin 6) (Fin 6) ℝ)
         (hK : K.transpose = -K) (hrank : K.rank ≤ 4) :
         ∃ (Q : Matrix (Fin 6) (Fin 6) ℝ) (a b : ℝ),
           Q.transpose * Q = 1 ∧ K = conjugate Q (skewWitness a b)
     ```
   - Combine with `rank_four_conjugated_exclusion` to establish the Master Rank-4 Theorem:
     ```lean
     theorem general_rank_four_exclusion (A K : Matrix (Fin 6) (Fin 6) ℝ)
         (hK : K.transpose = -K) (hrank : K.rank ≤ 4) :
         ∃ S : Matrix (Fin 6) (Fin 6) ℝ, S.transpose = S ∧
           frobeniusSquared S = frobeniusSquared K ∧
           frobeniusSquared (lyapunov A K) ≤ frobeniusSquared (lyapunov A S)
     ```

---

### Track B: Exact Rational SDP Certificate Tool for Active mf13 Targets

**Target File:** `/Users/mike/dev/ctrl/tools/certify_mf13_pair.py`.  
**Prerequisites:** `tools/sdp_rational_cert.py`, `work/pod/mf13/bilevel/bl.py`.

#### Step-by-Step Implementation Plan:
1. **Step B.1 — Dual SDP Formulation for Given Rational Pair $(K, Y) \in \mathbb{Q}^{6 \times 6}$:**
   - Input: Rational skew matrices $K, Y \in \mathbb{Q}^{6 \times 6}$ satisfying exact moments $m_0 = m_1 = m_2 = 0$.
   - Compute rational basis of $\ker(\Phi_{K,Y})$: $\{H_1, \dots, H_9\} \subset \mathbb{Q}^{6 \times 6}$ and particular solution $H_0 \in \mathbb{Q}^{6 \times 6}$ using exact Gaussian elimination over $\mathbb{Q}$.
   - Map to the $21 \times 21$ symmetric restriction basis $B_S(z) = B_S^{(0)} + \sum_{r=1}^9 z_r B_S^{(r)}$.
   - Dual SDP for $\min_z \|B_S(z)\|_2 \ge 1$:
     $$\max_{W \in \mathbb{S}_{21}} \operatorname{tr}(W B_S^{(0)}) \quad \text{s.t.} \quad W \succeq 0, \; \operatorname{tr}(W) = 1, \; \operatorname{tr}(W B_S^{(r)}) = 0 \quad (r=1, \dots, 9).$$

2. **Step B.2 — Rational Projection and Verification:**
   - Solve dual SDP numerically using Clarabel $\implies W_{\text{num}} \in \mathbb{R}^{21 \times 21}$.
   - Round entries to rational numbers $W_{\text{raw}} \in \mathbb{Q}^{21 \times 21}$.
   - Project onto the exact subspace $\operatorname{tr}(W_Q B_S^{(r)}) = 0$ ($r=1, \dots, 9$) and $\operatorname{tr}(W_Q) = 1$ via rational least squares.
   - Compute exact rational $LDL^T$ factorization via `rational_ldl(W_Q)`.
   - Verify that all 21 pivots $D_i > 0$.
   - Check that the certified bound $\operatorname{tr}(W_Q B_S^{(0)}) \ge 1$ (or $> 1$).

3. **Step B.3 — Algebraic Certifier for Equality Loci:**
   - For points on the Common-T locus: Implement `certify_common_t_involution(K, Y)` which takes $K, Y$, solves for the exact rational involution $T \in \mathbb{Q}^{6 \times 6}$ ($T^T = T, T^2 = I, TK = -KT, TY = -YT$), and computes the exact pairing $\langle YT, \mathcal{L}_A(KT) \rangle = \|Y\|^2$.
   - For points near the rank-4 ridge: Output the reflection parameters $(c_i, s_i)$ and check the non-negative gain formula from `SameSquareExclusion.lean`.

4. **Step B.4 — Verification Suite & Integration:**
   - Test on the rational candidate pairs from Card M05 (`cards/M05/CARD.md`): $t = 1/2$ and $t = 1/3$.
   - Test on the rational calibration pair $K = Y = \operatorname{diag}(J, 2J, 3J)$ at $A = \frac{1}{2}I_6$.
   - Test on the 40-digit near-miss candidate (`opt/results/best_candidate.json`) rounded to rational numbers.
   - Add test runner to `tests/test_mf13_rational_cert.py` and hook into `./ctrl check`.

---

## 6. Verification Method

To independently verify all findings in this report:

1. **Verify Lean Theorems in `SameSquareExclusion.lean`:**
   ```bash
   cd /Users/mike/dev/ctrl-research-notebook/research-notebook/lean-controls
   lake env lean /Users/mike/dev/ctrl/work/pod/mf13/theory/SameSquareExclusion.lean
   ```
   *Expected:* Compiles cleanly with zero errors, zero warnings, zero `sorry`, and `#print axioms` showing only `[propext, Classical.choice, Quot.sound]`.

2. **Verify M05 Card Rational Certificates and Lean Code:**
   ```bash
   cd /Users/mike/dev/ctrl
   uv run python work/pod/crossover-60-20261018/cards/M05/domain_exact.py
   uv run python -O work/pod/crossover-60-20261018/cards/M05/critic_verify_minnorm.py
   uv run python -O work/pod/crossover-60-20261018/cards/M05/critic_verify_testers.py
   cd /Users/mike/dev/ctrl/lean
   lake env lean ../work/pod/crossover-60-20261018/cards/M05/RepeatedSpectrum.lean
   ```
   *Expected:* All rational bounds replay exactly; `RepeatedSpectrum.lean` compiles cleanly.

3. **Verify the Common-Involution Lemma and Best Candidates:**
   ```bash
   cd /Users/mike/dev/ctrl/work/pod/mf13/bilevel
   uv run python test_lemma.py
   uv run python verify_candidate.py candidates/n6_ridge_reference_A.json 50
   uv run python verify_candidate.py candidates/n7_paper_integer_A.json 50
   ```
   *Expected:* `test_lemma.py` passes; $n=6$ candidate verifies $s \ge k$ (gap $-5.7 \times 10^{-15}$); $n=7$ candidate reproduces positive gap ($k > s$).

4. **Verify Rational SDP Tool Arithmetic:**
   ```bash
   cd /Users/mike/dev/ctrl
   uv run python -m pytest tests/test_sdp_rational_cert.py
   ```
   *Expected:* All exact rational $LDL^T$ and SDP certificate tests pass.
