# Operator Theory & Formal Methods Notes: MF-13 ($n=6$ Byers–Nash Problem)

**Date:** 2026-10-18
**Pod Member:** Operator Theorist / Formal Methods (`/Users/mike/dev/ctrl/work/pod/mf13/theory/`)

---

## 1. Precise Requirements for a Strict $n=6$ Counterexample

Let $\mathcal{L}_A(X) = A X + X A^T$ on $\mathbb{R}^{n \times n}$, equipped with the Frobenius norm $\|X\|_F = \sqrt{\operatorname{tr}(X^T X)}$, and let $E_A(X) = \|\mathcal{L}_A(X)\|_F^2$.
Since $\mathcal{L}_A$ preserves the orthogonal decomposition $\mathbb{R}^{n \times n} = \mathbb{S}_n \oplus \mathbb{K}_n$,
$$\|\mathcal{L}_A\| = \max\big\{s(A),\, k(A)\big\}, \qquad s(A) := \|\mathcal{L}_A|_{\mathbb{S}_n}\|, \quad k(A) := \|\mathcal{L}_A|_{\mathbb{K}_n}\|.$$

### Theorem 1.1 (Rank-4 Same-Square Exclusion — Lean-Verified in `SameSquareExclusion.lean`)
For every real skew-symmetric matrix $K \in \mathbb{K}_n$ of rank at most $4$ and every $A \in \mathbb{R}^{n \times n}$, there exists a symmetric matrix $S \in \mathbb{S}_n$ with the **same square** ($S^2 = -K^2$, hence $\|S\|_F = \|K\|_F$ and identical singular values) such that
$$E_A(K) \le E_A(S).$$

**Proof Summary (Formalized in Lean 4):**
1. **Formula (1) (`same_square_energy_diff`):** For any $S \in \mathbb{S}_n, K \in \mathbb{K}_n$ with $S^2 = -K^2$, expanding $\operatorname{tr}(\mathcal{L}_A(X)^T \mathcal{L}_A(X))$ cancels the $\operatorname{tr}(A^T A X^2)$ terms and yields:
   $$E_A(S) - E_A(K) = 2 \operatorname{tr}\!\big((A S)^2 + (A K)^2\big). \tag{1}$$
2. **Orthogonal Support Decomposition:** In an orthogonal basis where $K = \operatorname{diag}(K_{\text{supp}}, 0)$, any $S = \operatorname{diag}(S_{\text{supp}}, 0)$ with $S_{\text{supp}}^2 = -K_{\text{supp}}^2$ has the exact same coupling to the orthogonal complement: if $A = \begin{pmatrix} B & C \\ D & E \end{pmatrix}$, then $E_A(X) = E_B(X_{\text{supp}}) + 2\|D X_{\text{supp}}\|_F^2$, and $\|D S_{\text{supp}}\|_F^2 = -\operatorname{tr}(D K_{\text{supp}}^2 D^T) = \|D K_{\text{supp}}\|_F^2$.
3. **2×2 Block Expansion (Formula (2)):** For $K_{\text{supp}} = \operatorname{diag}(a J, b J)$ ($J = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$) and $S_{\text{supp}} = \operatorname{diag}(a R_1, b R_2)$ where $R_i = R(\theta_i) = \begin{pmatrix} \cos\theta_i & \sin\theta_i \\ \sin\theta_i & -\cos\theta_i \end{pmatrix}$ are symmetric reflections ($R_i^2 = I_2 = -J^2$):
   - **Diagonal blocks (`block2_diag_trace_identity`):** Using the Cayley–Hamilton identity $\operatorname{tr}(M^2) = (\operatorname{tr} M)^2 - 2\det M$ and $\det R_i = -1 = -\det J$, the $\det B_{ii}$ terms cancel:
     $$\operatorname{tr}((B_{ii} R_i)^2 + (B_{ii} J)^2) = (\operatorname{tr}(B_{ii} R_i))^2 + (\operatorname{tr}(B_{ii} J))^2 \ge 0.$$
   - **Single off-diagonal cross term (`signed_svd_2x2_exists`, `block2_cross_trace_cancel`):** When $\operatorname{rank}(K) \le 4$, there is at most one cross term $4ab\operatorname{tr}(B_{12} R_2 B_{21} R_1 + B_{12} J B_{21} J)$. By applying an explicit $SO(2) \times SO(2)$ signed SVD $U^T B_{12} V = D$ (diagonal), since $SO(2)$ commutes with $J$ (`rot2_preserves_J2`), choosing $R_1 = R_2 = X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ in the rotated basis makes the cross term vanish identically:
     $$\operatorname{tr}(D X N X + D J N J) = 0 \quad \forall \text{ diagonal } D, \, \forall N \in \mathbb{R}^{2\times 2}.$$
   - Consequently, in the rotated basis with $R_1 = R_2 = X$, Formula (1) simplifies to (`gain_difference`):
     $$E_A(S) - E_A(K) = 4 a^2 \big((B_{11})_{01}^2 + (B_{11})_{10}^2\big) + 4 b^2 \big((B_{22})_{01}^2 + (B_{22})_{10}^2\big) \ge 0.$$

### Corollary 1.2 (Necessary Rank Conditions for a Strict $n=6$ Counterexample)
Suppose $A \in \mathbb{R}^{6 \times 6}$ satisfies $k(A) > s(A)$. Scale $A$ by $1/k(A)$ so that $k(A) = 1 > s(A)$, and let $K, Y \in \mathbb{K}_6$ with $\|K\|_F = \|Y\|_F = 1$ be right and left skew singular witnesses:
$$A K + K A^T = Y, \qquad A^T Y + Y A = K. \tag{3}$$
Then:
1. $\operatorname{rank}(K) = 6$ ($\det K \ne 0$), by Theorem 1.1 applied to $(A, K)$.
2. $\operatorname{rank}(Y) = 6$ ($\det Y \ne 0$), by Theorem 1.1 applied to $(A^T, Y)$, since $\|\mathcal{L}_{A^T}|_{\mathbb{S}_6}\| = s(A)$ and $\|\mathcal{L}_{A^T}|_{\mathbb{K}_6}\| = k(A)$.
3. Any same-square symmetric comparator ($S^2 = -K^2$) on $\mathbb{R}^6$ only uses 3 reflection angles $(\theta_1, \theta_2, \theta_3)$, whereas a general unit symmetric matrix $S \in \mathbb{S}_6$ has 20 degrees of freedom (including 5 independent eigenvalue ratios).

---

## 2. Structural Analysis of the Kressner–Vandereycken $7 \times 7$ Counterexample (arXiv:2608.20875)

We analyzed the exact integer counterexample $A \in \mathbb{Z}^{7 \times 7}$ from Theorem 2 of Kressner & Vandereycken (August 2026) (`analyze_7x7.py`, `analyze_7x7_part2.py`, `test_same_square_7x7.py`):
$$A = \begin{pmatrix}
0 & 0 & 0 & 0 & 0 & 0 & 0 \\
0 & 0 & 0 & 0 & 0 & 0 & 0 \\
6 & -5 & -13 & 0 & 0 & 0 & 0 \\
-14 & -18 & 0 & 0 & 0 & 0 & 0 \\
12 & -12 & 11 & 0 & 0 & 0 & 0 \\
0 & 0 & 0 & -6 & 0 & -14 & 0 \\
0 & 0 & 0 & 6 & -18 & 0 & 0
\end{pmatrix}, \qquad s(A)^2 \approx 1195.593985 < 1196 < k(A)^2 \approx 1196.025224.$$

### Key Structural Findings:
1. **Block & Spectral Structure of $A$:**
   - $\operatorname{rank}(A) = 5$: rows 1, 2 and column 7 of $A$ are identically zero.
   - Eigenvalues of $A$: $\{-14, -13, 0, 0, 0, 0, 0\}$.
   - Up to independent row/column permutations, the nonzero $5 \times 6$ submatrix of $A$ is the orthogonal direct sum of a $3 \times 3$ block $A_1$ and a $2 \times 3$ block $A_2$, with $\|A\|_2^2 < 1196$.
2. **Rank and Kernel Alignment of $K_{\text{opt}}$ and $Y_{\text{opt}}$:**
   - Because $n=7$ is odd, every skew-symmetric matrix has even rank $\le 6$. Both the exact top right skew singular witness $K_{\text{opt}}$ and left witness $Y_{\text{opt}}$ have **rank 6**:
     $$\sigma(K_{\text{opt}}) \approx (0.59895, 0.59895,\, 0.36582, 0.36582,\, 0.08623, 0.08623,\, 0),$$
     $$\sigma(Y_{\text{opt}}) \approx (0.61437, 0.61437,\, 0.32538, 0.32538,\, 0.12914, 0.12914,\, 0).$$
   - Crucially, **their 1D kernels are NOT aligned:** $|\langle \ker K_{\text{opt}}, \ker Y_{\text{opt}} \rangle| \approx 0.15523$ ($\theta \approx 81.1^\circ$).
3. **Why $n=7$ Works While the Projected $6 \times 6$ Submatrix $B_6$ Does NOT:**
   - Change basis by $Q \in O(7)$ so that $K_Q = Q^T K_{\text{opt}} Q = \operatorname{diag}(K_6, 0)$, where $K_6 \in \mathbb{K}_6$ is full-rank, and partition
     $$A_Q = Q^T A Q = \begin{pmatrix} B_6 & c_{6 \times 1} \\ d_{1 \times 6} & e_{1 \times 1} \end{pmatrix}.$$
   - Then for any $X = \operatorname{diag}(X_6, 0)$ supported on the first 6 coordinates:
     $$E_{A_Q}(X) = E_{B_6}(X_6) + 2 \|d_{1 \times 6} X_6\|_F^2 = E_{B_6}(X_6) + 2 \operatorname{tr}(d_{1 \times 6} X_6 X_6^T d_{1 \times 6}^T).$$
   - Numerically (`test_same_square_7x7.py`):
     $$E_{A_Q}(K_Q) = \underbrace{E_{B_6}(K_6)}_{1025.0842} + \underbrace{2 \|d_{1 \times 6} K_6\|_F^2}_{170.9410} = 1196.0252.$$
   - Over all **same-square** symmetric matrices $S_6 \in \mathbb{S}_6$ ($S_6^2 = -K_6^2$), the $d_{1 \times 6}$ contribution is fixed at $170.9410$, while the 3-block same-square maximum on $B_6$ is:
     $$\max_{S_6^2 = -K_6^2} E_{B_6}(S_6) = 1012.3038 < E_{B_6}(K_6) = 1025.0842,$$
     giving $E_{A_Q}(\operatorname{diag}(S_6, 0)) \le 1183.2448 < 1196.0252$.
   - **However, on the $6 \times 6$ matrix $B_6$ itself, the unconstrained symmetric norm is strictly LARGER than the skew norm:**
     $$\|\mathcal{L}_{B_6}|_{\mathbb{S}_6}\|^2 = 1149.8184 > \|\mathcal{L}_{B_6}|_{\mathbb{K}_6}\|^2 = 1090.3284 > E_{B_6}(K_6) = 1025.0842!$$
   - **The Mechanism of $n=7$:** In $n=7$, the 7th row $d_{1 \times 6}$ acts as an external covariance penalty $2 \operatorname{tr}(d_{1 \times 6} S_6^2 d_{1 \times 6}^T)$ (plus couplings to the 7th coordinate) that punishes any symmetric comparator $S_6$ whose square $S_6^2$ deviates from $-K_6^2$, preventing $B_6$'s true symmetric maximizer (which has a different square $S_6^2 \ne -K_6^2$) from achieving $1196$ in $\mathbb{R}^7$.
   - **In $n=6$, there is NO 7th coordinate ($d_{1 \times 6} = 0$) to lock $S^2$ to $-K^2$.**

---

## 3. Necessary Conditions, Symplectic Structure, and Exact Parameter Count for $n=6$

Assume $K, Y \in \mathbb{K}_6$ are invertible with $\|K\|_F = \|Y\|_F = 1$.

### 3.1 Linear Elimination and Converse (`CoupledLyapunov.lean` & `SameSquareExclusion.lean`)
Setting $H = A K - \frac{1}{2} Y$ (or $B = 2H = A K - K A^T$ division-free), the coupled equations (3) are **equivalent** (`coupled_elimination` and `coupled_elimination_converse`) to:
$$H^T = H, \qquad A = \left(H + \frac{1}{2} Y\right) K^{-1}, \qquad \Phi_{K,Y}(H) := (K Y) H - H (Y K) = K^3 - \frac{1}{2}(Y^2 K + K Y^2). \tag{4}$$

### 3.2 Symplectic Self-Adjointness of $T = Y K$ and Spectral Duplication
Define the nondegenerate symplectic form $\omega(x, y) := x^T K^{-1} y$ on $\mathbb{R}^6$. Since $K^T = -K$ and $Y^T = -Y$, the operator $T = Y K$ satisfies:
$$K^{-1} (Y K) = (K^{-1} Y) K = (Y K)^T K^{-1} \implies \omega(T x, y) = \omega(x, T y).$$
That is, **$T = Y K$ is self-adjoint with respect to the symplectic form $\omega$.**
By the structure theorem for symplectic-self-adjoint operators:
- **Every eigenvalue (and every Jordan block) of $Y K$ has even multiplicity.**
- In dimension $n=6$, $Y K$ has at most **3 distinct eigenvalues** $\mu_1, \mu_2, \mu_3$ (either 3 real pairs or 1 real pair and 1 complex-conjugate pair of pairs), each corresponding to a 2-dimensional $\omega$-nondegenerate $T$-invariant subspace.
- Therefore, the minimal polynomial of $Y K$ generically has degree $3$:
  $$\min\text{poly}_{Y K}(t) = (t - \mu_1)(t - \mu_2)(t - \mu_3).$$

### 3.3 Exact Cokernel and Kernel of $\Phi_{K,Y} : \mathbb{S}_6 \to \mathbb{K}_6$
1. **Adjoint of $\Phi_{K,Y}$:** For any $W \in \mathbb{K}_6$ and $H \in \mathbb{S}_6$,
   $$\langle W, \Phi_{K,Y}(H) \rangle_F = -\operatorname{tr}\!\big(W ((K Y) H - H (Y K))\big) = -\operatorname{tr}\!\big((W K Y - Y K W) H\big).$$
   Since $(W K Y - Y K W)^T = -Y K W + W K Y = W K Y - Y K W \in \mathbb{S}_6$, we have:
   $$W \in \ker(\Phi_{K,Y}^*) \iff W K Y = Y K W \iff (W K)(Y K) = (Y K)(W K).$$
2. **Explicit Basis of $\ker(\Phi_{K,Y}^*)$:** For generic $(K, Y)$ (where $\mu_1, \mu_2, \mu_3$ are distinct), the $\omega$-self-adjoint operators commuting with $T = Y K$ are spanned by $I_6, T, T^2$. Multiplying on the right by $K^{-1}$ gives an explicit 3-dimensional basis of $\ker(\Phi_{K,Y}^*) \subset \mathbb{K}_6$:
   $$W_0 = K^{-1}, \qquad W_1 = Y, \qquad W_2 = Y K Y.$$
   Thus $\operatorname{rank}(\Phi_{K,Y}) = 15 - 3 = 12$ and $\dim \ker(\Phi_{K,Y}) = 21 - 12 = 9$.
3. **Why Three Trace Moments Are Necessary AND Generically Sufficient:**
   Pairing the right-hand side $\text{RHS}(K,Y) = K^3 - \frac{1}{2}(Y^2 K + K Y^2)$ with $W_j = (Y K)^j K^{-1}$ ($j = 0, 1, 2$) yields:
   $$-\operatorname{tr}\!\big(W_j \text{RHS}(K,Y)\big) = \operatorname{tr}\!\big((Y K)^j (Y^2 - K^2)\big) =: m_j(K, Y).$$
   Hence, for generic full-rank $(K, Y)$, **Equation (4) admits a symmetric solution $H \in \mathbb{S}_6$ if and only if $m_0(K,Y) = m_1(K,Y) = m_2(K,Y) = 0$!**
   (Higher moments $m_j(K,Y) = 0$ for $j \ge 3$ follow automatically from $m_0 = m_1 = m_2 = 0$ because $(Y K)^3 \in \operatorname{span}\{I, Y K, (Y K)^2\}$.)
4. **Structure of the 9D Kernel $\ker(\Phi_{K,Y}) \subset \mathbb{S}_6$:**
   Writing $H = K S$, $H \in \ker(\Phi_{K,Y}) \iff [S, Y K] = 0$ and $(K S)^T = K S$. On each of the three 2D symplectic eigenspaces of $Y K$, $K S$ restricts to an arbitrary $2 \times 2$ symmetric matrix (3 parameters), giving $3 \times 3 = 9$ free real parameters $z \in \mathbb{R}^9$.

### 3.4 Canonical Form and Exact Dimension Count
Modulo scaling $\|K\|_F = 1$ and simultaneous orthogonal conjugation $Q \in O(6)$:
- Put $K = \operatorname{diag}(a J, b J, c J)$ with $a \ge b \ge c > 0$ and $a^2 + b^2 + c^2 = 1/2$: **2 parameters**.
- The stabilizer of $K$ in $O(6)$ is $SO(2) \times SO(2) \times SO(2)$ (dimension 3).
- $Y \in \mathbb{K}_6$ has 15 entries, minus 3 stabilizer angles, minus 3 moment constraints $m_0 = m_1 = m_2 = 0$: **9 parameters**.
- Thus the moduli space of compatible full-rank singular pairs $(K, Y)$ has **11 outer parameters**, and each pair has a **9-dimensional affine space** of compatible matrices $A(z)$ ($z \in \mathbb{R}^9$) over which $s(A(z)) = \sigma_{\max}(B_S(z))$ is **convex**.

---

## 4. Structural Evidence on $n=6$: Plausibility of Proof vs. Counterexample

We investigated both universal lower-bound comparators and numerical minimization on the 11D+9D reduced space (`verify_involution_bound.py`, `test_general_compatible.py`, `check_dist_K.py`, `test_outer_opt.py`):

1. **Exact Involutive Submanifold ($Y = \pm Q K Q$ with $Q = Q^T \in O(6)$):**
   - Whenever $Y = \pm Q K Q$ for a symmetric orthogonal involution $Q$, conjugation by $Q$ maps $Y K$ to $K Y = (Y K)^T$ and $Y^2 - K^2$ to $-(Y^2 - K^2)$, so **all trace moments $m_j(K, Y) = 0$ vanish identically**.
   - **Analytical Invariant:** For any invertible symmetric $S \in \mathbb{S}_6$, $\operatorname{tr}(S^{-1} (H K^{-1} S - S K^{-1} H)) = 0$ for **all** $H \in \mathbb{S}_6$. Consequently,
     $$\operatorname{tr}(S^{-1} \mathcal{L}_A(S)) = 2 \operatorname{tr}(A) = \operatorname{tr}(Y K^{-1})$$
     is **completely independent of $H$**.
2. **Numerical Behavior of $\min_{z \in \mathbb{R}^9} s(A(z))$ on Full-Rank Compatible Pairs $(K, Y)$:**
   - Across random full-rank compatible pairs $(K, Y)$ (`check_dist_K.py`), $\min_{z \in \mathbb{R}^9} s(A(z))$ consistently lies in $[1.32, 6.50]$, strictly above $1$.
   - When we run outer optimization (`test_outer_opt.py`) to minimize $f(K, Y) = \min_{z \in \mathbb{R}^9} s(A(z))$ with a full-rank barrier $\sigma_{\min}(K), \sigma_{\min}(Y) \ge 0.08$, the optimizer drives $f(K, Y)$ down to $1.00000010$ by driving $[Y, K] \to 0$ (i.e. $Y \to K$, where $A = \frac{1}{2} I_6$ gives $s(A) = k(A) = 1$).
   - When we add a non-commutativity barrier $\|[Y, K]\|_F \ge 0.15$ alongside $\sigma_{\min}(Y) \ge 0.10$, $f(K, Y)$ remains strictly above $1$.
3. **Assessment (Proof vs. Counterexample in $n=6$):**
   - **A positive proof for $n=6$ is significantly more plausible than a counterexample,** provided one uses **different-square symmetric comparators ($S^2 \ne -K^2$)** or SDP duality on the 9D affine family $A(z)$.
   - Specifically, the $7 \times 7$ counterexample relies critically on the 7th coordinate to penalize $S^2 \ne -K^2$ while $K$ has rank 6. In $n=6$, no such external coordinate exists, and the 9 free parameters $z \in \mathbb{R}^9$ in $H$ appear unable to simultaneously suppress all 21 dimensions of $\mathbb{S}_6$ below $1$.
   - How a proof for $n=6$ can work: for any compatible pair $(K, Y)$, construct a dual certificate (a positive semidefinite combination of symmetric test matrices $S_1, \dots, S_r \in \mathbb{S}_6$, such as $I_6$, $(Y K + K Y)$, and projections onto the 3 symplectic eigenspaces of $Y K$) whose $H$-dependence cancels via the Sylvester equation $\Phi_{K,Y}(H) = \text{RHS}(K,Y)$!

---

## 5. Lean 4 Formalization Summary (`SameSquareExclusion.lean`)

File path: `/Users/mike/dev/ctrl/work/pod/mf13/theory/SameSquareExclusion.lean`
Compiled via: `cd /Users/mike/dev/ctrl-research-notebook/research-notebook/lean-controls && lake env lean /Users/mike/dev/ctrl/work/pod/mf13/theory/SameSquareExclusion.lean`
Toolchain: `leanprover/lean4:v4.35.0`

All 21 theorems in `SameSquareExclusion.lean` compile with **zero errors, zero warnings, and zero `sorry`**, depending only on the standard Lean axioms `[propext, Classical.choice, Quot.sound]`:

1. `same_square_energy_diff`: Formula (1), `E_A(S) - E_A(K) = 2 * tr((A*S)^2 + (A*K)^2)` for arbitrary `n × n` real matrices with `Sᵀ = S`, `Kᵀ = -K`, `S * S = -(K * K)`.
2. `same_square_comparison_of_trace_nonneg`: `0 ≤ tr((A*S)^2 + (A*K)^2) → E_A(K) ≤ E_A(S)`.
3. `block2_diag_trace_identity`: `tr((B * refl2 c s)^2 + (B * J2)^2) = (tr(B * refl2 c s))^2 + (tr(B * J2))^2` for `c^2 + s^2 = 1`.
4. `block2_diag_trace_nonneg`: `0 ≤ tr((B * refl2 c s)^2 + (B * J2)^2)`.
5. `rank_two_dim2_comparison`: `E_B(refl2 c s) - E_B(J2) = 2 * ((tr(B * refl2 c s))^2 + (tr(B * J2))^2)` in `Fin 2`.
6. `block2_cross_trace_cancel`: `tr(D * X2 * N * X2 + D * J2 * N * J2) = 0` for any diagonal `D : Mat2` (`D 0 1 = 0`, `D 1 0 = 0`) and arbitrary `N : Mat2`.
7. `rot2_preserves_J2`: `(rot2 c s)ᵀ * J2 * rot2 c s = J2` for `c^2 + s^2 = 1`.
8. `signed_svd_2x2_offdiag`: algebraic vanishing of the `(0,1)` and `(1,0)` entries of `(rot2 cu su)ᵀ * B * rot2 cv sv`.
9. `unit_normal_exists`: `∀ p q : ℝ, ∃ c s : ℝ, c^2 + s^2 = 1 ∧ p * s - q * c = 0`.
10. `half_angle_exists`: `∀ c s : ℝ, c^2 + s^2 = 1 → ∃ x y : ℝ, x^2 + y^2 = 1 ∧ x^2 - y^2 = c ∧ 2 * x * y = s`.
11. `signed_svd_angles_exist`: unconditional existence of `SO(2) × SO(2)` signed-SVD angles for any 4 real entries.
12. `signed_svd_2x2_exists`: unconditional 2×2 signed SVD (`∀ B : Mat2, ∃ cu su cv sv, ...`).
13. `rank_two_gain_difference`: exact gain difference `4 * a^2 * ((A 0 1)^2 + (A 1 0)^2)` for `skewWitness a 0` in `Fin 6`.
14. `rank_two_gain_comparison`: `E_A(skewWitness a 0) ≤ E_A(symmetricWitness a 0)` in `Fin 6`.
15. `rank_two_conjugated_exclusion`: unconditional rank-2 exclusion in any orthogonal basis of `Fin 6`.
16. `blockRot6_orthogonal`: orthogonality of the `SO(2) × SO(2) × I_2` block rotation `blockRot6 cu su cv sv` in `Fin 6`.
17. `blockRot6_preserves_skewWitness`: `conjugate (blockRot6 cu su cv sv) (skewWitness a b) = skewWitness a b`.
18. `rank_four_same_square_exclusion_rot`: rank-4 same-square exclusion given diagonalizing `SO(2) × SO(2)` angles.
19. `rank_four_same_square_exclusion_unconditional`: **unconditional** rank-4 same-square exclusion in `Fin 6` for `skewWitness a b` and arbitrary `A : Mat`.
20. `rank_four_conjugated_exclusion`: **unconditional** rank-4 same-square exclusion in any orthogonal basis `Q` of `Fin 6`.
21. `coupled_elimination_converse`: division-free converse of the coupled-pair reduction in arbitrary dimension `n`.
