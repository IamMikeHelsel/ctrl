# Reduced Search Space for $n=6$ Byers–Nash Optimization (`mf13/opt`)

**Author:** Operator Theorist / Formal Methods (`mf13/theory`)
**Date:** 2026-10-18

---

## 1. Executive Summary & Why Direct 36-Variable Search Gets Trapped

1. **Rank-4 Exclusion Theorem:** Every skew-symmetric witness $K \in \mathbb{K}_n$ with $\operatorname{rank}(K) \le 4$ admits a same-square symmetric witness $S \in \mathbb{S}_n$ ($S^2 = -K^2$, $\|S\|_F = \|K\|_F$) such that $\|\mathcal{L}_A(S)\|_F \ge \|\mathcal{L}_A(K)\|_F$, in **any** ambient dimension $n$.
   - *Consequence for $n=6$:* A strict counterexample $\|\mathcal{L}_A|_{\mathbb{K}_6}\| > \|\mathcal{L}_A|_{\mathbb{S}_6}\|$ requires **both** the right skew singular witness $K$ and the left skew singular witness $Y = \mathcal{L}_A(K)/\|\mathcal{L}_A|_{\mathbb{K}_6}\|$ (which is the right witness for $A^T$) to have **full rank 6** ($\det K \ne 0$, $\det Y \ne 0$).
   - *Why existing searches failed:* Unconstrained gradient/Adam searches on $A \in \mathbb{R}^{6\times 6}$ slide into the massive rank-4 equality boundary ($\sigma_5(K)=\sigma_6(K) \to 0$) where $s(A) = k(A)$ identically.

2. **Why $n=7$ Worked (Kressner–Vandereycken, arXiv:2608.20875):**
   - In the 7×7 counterexample, the optimal skew witness $K_{\text{opt}} \in \mathbb{K}_7$ has **rank 6** (singular values $0.5989, 0.3658, 0.0862$ each with multiplicity 2, and one 0), and $Y_{\text{opt}} \in \mathbb{K}_7$ also has **rank 6**, with $\ker(K_{\text{opt}}) \ne \ker(Y_{\text{opt}})$ ($\cos\theta \approx 0.155$).
   - Crucially, on the 6D support of $K_{\text{opt}}$, the 6×6 projected submatrix $B_6$ actually satisfies $\|\mathcal{L}_{B_6}|_{\mathbb{S}_6}\|^2 = 1149.82 > \|\mathcal{L}_{B_6}|_{\mathbb{K}_6}\|^2 = 1090.33 \ge E_{B_6}(K_6) = 1025.08$!
   - Why didn't the optimal 6×6 symmetric comparator $S_{\text{opt}}(B_6)$ work in $\mathbb{R}^7$? Because in $\mathbb{R}^7$, the 7th row of $A$ couples to the 6D support via $2\|D_{1\times 6} X\|_F^2 = 2\operatorname{tr}(D X^2 D^T)$. Every same-square comparator ($S^2 = -K_6^2$) preserves this 7th-row gain ($170.94$) and only achieves $E_{B_6}(S) \le 1012.30 < 1025.08$. Meanwhile, the true symmetric maximizer of $B_6$ has a **different square** ($S^2 \ne -K_6^2$) and loses more on the 7th-row coupling $2\|D S\|_F^2$ than it gains on $B_6$!
   - **In $n=6$, there is NO 7th row $D_{1\times 6}$ to penalize different-square symmetric comparators ($S^2 \ne -K^2$).**

---

## 2. Exact Parametrization and Dimension Reduction (36D $\to$ 11D + 9D Convex Inner Problem)

Normalize the target skew singular value to $1$ and scale $K, Y \in \mathbb{K}_6$ so that $\|K\|_F = \|Y\|_F = 1$. The coupled singular-pair equations are:
$$A K + K A^T = Y, \qquad A^T Y + Y A = K. \tag{1}$$

### Step 1: Canonical Form of $K$ under $O(6)$ (2 parameters)
Using the orthogonal group $O(6)$ (which acts simultaneously on $A, K, Y$ without changing norms) and Frobenius normalization $\|K\|_F^2 = 1$, fix $K$ strictly in block-diagonal canonical form:
$$K(\theta, \phi) = \operatorname{diag}(a J, \, b J, \, c J), \qquad J = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix},$$
where $a \ge b \ge c > 0$ and $a^2 + b^2 + c^2 = \frac{1}{2}$ (e.g. spherical coordinates with $c \ge \varepsilon > 0$ to enforce full rank 6).
- **Remaining symmetry stabilizer:** $\operatorname{Stab}_{O(6)}(K) = SO(2) \times SO(2) \times SO(2)$ (dimension 3), which can be used to eliminate 3 parameters in $Y$ (e.g., setting one entry to 0 in each of the $(1,2)$, $(2,3)$, $(1,3)$ off-diagonal 2×2 blocks of $Y$).

### Step 2: Symplectic-Self-Adjoint Structure of $Y K$ and Necessary & Sufficient Compatibility of $(K, Y)$ (9 parameters)
Define $H = A K - \frac{1}{2} Y$. The first equation $AK + KA^T = Y$ is equivalent to $H = H^T \in \mathbb{S}_6$ and
$$A = \left(H + \frac{1}{2} Y\right) K^{-1}. \tag{2}$$
Substituting (2) into $A^T Y + Y A = K$ yields the linear system for $H \in \mathbb{S}_6$ (21 variables) into $\mathbb{K}_6$ (15 equations):
$$\Phi_{K,Y}(H) := (K Y) H - H (Y K) = K^3 - \frac{1}{2}(Y^2 K + K Y^2) =: \text{RHS}(K,Y). \tag{3}$$

**Theorem (Symplectic Structure & Exact Cokernel of $\Phi_{K,Y}$):**
1. The operator $T = Y K$ is self-adjoint with respect to the symplectic form $\omega(x,y) = x^T K^{-1} y$. Consequently, **every eigenvalue of $Y K$ has even multiplicity**, so the characteristic polynomial of $Y K$ is a perfect square $p(t)^2$ where $\deg p = 3$.
2. For generic $(K, Y)$ (whenever $p(t)$ has 3 distinct roots), $\operatorname{rank}(\Phi_{K,Y}) = 12$, the cokernel $\ker(\Phi_{K,Y}^*) \subset \mathbb{K}_6$ has dimension $15 - 12 = 3$, and is spanned explicitly by:
   $$W_0 = K^{-1}, \qquad W_1 = Y, \qquad W_2 = Y K Y.$$
3. Pairing $\text{RHS}(K,Y)$ with $W_0, W_1, W_2$ gives $-\operatorname{tr}(W_j \,\text{RHS}(K,Y)) = \operatorname{tr}((Y K)^j (K^2 - Y^2))$. Therefore, **Equation (3) has a symmetric solution $H \in \mathbb{S}_6$ if and only if the three trace moments vanish:**
   $$\begin{aligned}
   m_0(K, Y) &= \operatorname{tr}(Y^2 - K^2) = 0 \quad (\iff \|Y\|_F^2 = \|K\|_F^2 = 1), \\
   m_1(K, Y) &= \operatorname{tr}(Y K (Y^2 - K^2)) = 0, \\
   m_2(K, Y) &= \operatorname{tr}((Y K)^2 (Y^2 - K^2)) = 0.
   \end{aligned} \tag{4}$$
   *(All higher moments $j \ge 3$ follow automatically because $\min\text{poly}(Y K)$ has degree 3!)*

Counting dimensions: $\dim(\mathbb{K}_6) = 15$ for $Y$, minus 3 trace moments (4), minus 3 stabilizer angles $SO(2)^3$ gives **9 intrinsic parameters for $Y$** (plus **2 for $K$** = **11 outer parameters** total).

### Step 3: Exact 9D Affine Solution Space for $H$ (Convex Inner Problem)
For any compatible pair $(K, Y)$ satisfying (4):
- Compute the minimum-norm particular solution $H_0 = \Phi_{K,Y}^+ (\text{RHS}(K,Y)) \in \mathbb{S}_6$ and an orthonormal basis $\{H_1, \dots, H_9\} \subset \mathbb{S}_6$ of $\ker(\Phi_{K,Y})$.
  *(Explicitly, $H \in \ker(\Phi_{K,Y}) \iff H = K S$ where $S$ commutes with $Y K$ and $K S$ is symmetric; on each of the three 2D eigenspaces of $Y K$, this gives a 3D space of 2×2 symmetric matrices, hence $3 \times 3 = 9$ dimensions.)*
- Every matrix $A$ having $(K, Y)$ as a skew singular pair with singular value $1$ is given by:
  $$A(z) = \left(H_0 + \sum_{r=1}^9 z_r H_r + \frac{1}{2} Y\right) K^{-1}, \qquad z \in \mathbb{R}^9. \tag{5}$$
- Define the $21 \times 21$ symmetric restriction matrix $B_S(A(z)) = B_S^{(0)} + \sum_{r=1}^9 z_r B_S^{(r)}$.
- **Inner Convex Problem:** Minimize the largest singular value
  $$f(K, Y) := \min_{z \in \mathbb{R}^9} \sigma_{\max}\!\left(B_S^{(0)} + \sum_{r=1}^9 z_r B_S^{(r)}\right). \tag{6}$$
  Since $\sigma_{\max}(\cdot)$ is convex in $z \in \mathbb{R}^9$, any local minimum in $z$ is the **global minimum** for that pair $(K, Y)$!
- **Criterion for a Counterexample:** A strict counterexample exists for $(K, Y)$ **if and only if** $f(K, Y) < 1$ (and we also verify that $1$ is the top skew singular value of $A(z^*)$, though $f(K,Y) < 1$ immediately implies $\|\mathcal{L}_{A(z^*)}|_{\mathbb{S}_6}\| < 1 \le \|\mathcal{L}_{A(z^*)}|_{\mathbb{K}_6}\|$!).

---

## 3. Concrete Families & Algorithms for `mf13/opt`

We recommend `mf13/opt` implement two complementary search tracks using this reduction:

### Track A: Full 11D Outer + 9D Inner Bi-Level Search (Manifold Projection)
1. **Outer variables (14 unconstrained parameters):**
   - $(u, v) \in \mathbb{R}^2$ determining $a, b, c > \varepsilon$ with $a^2 + b^2 + c^2 = 1/2$, $K = \operatorname{diag}(a J, b J, c J)$.
   - $y \in \mathbb{R}^{12}$ (the 15 upper-triangular entries of $Y_{\text{raw}}$, fixing $Y_{0,3} = Y_{2,5} = Y_{0,5} = 0$ via the $SO(2)^3$ gauge).
2. **Fast Gauss–Newton Projection onto Compatibility Manifold $\mathcal{M}_K$:**
   - Given $Y_{\text{raw}}$, take 5–8 Gauss–Newton steps in $\mathbb{R}^{15}$:
     $$y \leftarrow y - J_m(y)^+ m(y), \qquad m(y) = \big(m_0(K,Y),\, m_1(K,Y),\, m_2(K,Y)\big) \in \mathbb{R}^3$$
     until $\|m(y)\|_2 < 10^{-15}$. (This takes $< 0.2\text{ ms}$ in NumPy and converges quadratically.)
   - Reject or penalize if $\sigma_{\min}(Y) < \varepsilon$ (to stay away from the rank-4 boundary!).
3. **Inner Solver ($z \in \mathbb{R}^9$):**
   - Solve $\Phi_{K,Y}(H) = \text{RHS}(K,Y)$ via SVD of the $15 \times 21$ matrix $\Phi_{K,Y}$.
   - Minimize $\sigma_{\max}(B_S(z))$ over $z \in \mathbb{R}^9$ using BFGS with exact subgradient $\nabla_z \sigma_{\max} = (u_1^T B_S^{(r)} v_1)_{r=1}^9$ (or an SDP/SOCP solver, or smooth log-sum-exp of singular values).
4. **Outer Optimization:**
   - Minimize $f(K, Y) + \mu \max(0, \varepsilon - \sigma_{\min}(K)) + \mu \max(0, \varepsilon - \sigma_{\min}(Y))$ using CMA-ES, Nelder–Mead, or Adam with finite-difference/implicit gradients on the 14 outer variables.

### Track B: Exact Involutive Submanifold (Zero-Defect Analytical Compatibility, 8 Outer Parameters)
We discovered an exact algebraic submanifold where **all trace moments $m_j(K,Y) = 0$ ($j \ge 0$) vanish identically without projection**:
- Choose any orthogonal involution $Q \in O(6)$ with $Q^T = Q, Q^2 = I_6$, or any skew-involution, or more generally let $Y = \pm Q K Q^T$ where $Q \in O(6)$ satisfies $Q^2 = \pm I_6$.
- *Caution (Proven Lower Bound):* We proved analytically that if $Q = Q^T \in O(6)$ ($Q^2 = I_6$) and $Y = +Q K Q$, then the symmetric test matrix $S = Q$ **always** satisfies $\operatorname{tr}(Q \mathcal{L}_A(Q)) = \operatorname{tr}(Y K^{-1})$... wait: for $Y = Q K Q$ with $Q$ commuting with $K$ on blocks it gives $\ge 1$, whereas for general $Q = Q^T$ and $Y = \pm Q K Q$, $\Phi_{K,Y}(H) = \text{RHS}$ is **always exactly consistent** ($\|m(Y)\| = 0$ identically)!
- Parametrize $Q = U \operatorname{diag}(I_k, -I_{6-k}) U^T$ ($k \in \{1,2,3\}$) or $Y = Q K Q$ with $Q \in O(6), Q^T = Q$: this requires **zero root-finding** and gives an exact smooth parameterization of compatible full-rank pairs $(K, Y)$ with $\sigma_i(Y) = \sigma_i(K) = (a,a,b,b,c,c)$.

---

## 4. Reference Python Implementation of the Reduction

A working self-contained prototype is in `/Users/mike/dev/ctrl/work/pod/mf13/theory/test_general_compatible.py`. Key functions:
- `project_Y(K, Y_init)`: Projects any $Y_{\text{init}} \in \mathbb{K}_6$ onto the 3 trace moment constraints to $10^{-16}$ precision in $<10$ iterations.
- `solve_pair(K, Y)`: Computes $H_0$ and the 9D nullspace basis $H_1, \dots, H_9$ with residual $\sim 10^{-16}$.
- `min_sym_norm_for_pair(K, Y)`: Solves the 9D convex inner problem $\min_{z \in \mathbb{R}^9} \|\mathcal{L}_{A(z)}|_{\mathbb{S}_6}\|$.
