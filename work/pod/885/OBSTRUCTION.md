# Obstruction and Algebraic Geometry Certificate: Column Extension for Erdős 885 $6 \times 4$ Grids

**Date**: 2026-10-19  
**Target**: Erdős Problem #885 ($k=5$, $6 \times 5$ square-sum grid)  
**Artifacts**: `tools/verify_885_geometry.py`, `tests/test_885_geometry.py`  
**Classification**: **Bounded search negative ($q \le 10^6$) + Faltings finiteness (non-effective)**  

---

## 1. Executive Summary

Erdős Problem #885 asks whether for every $k$, there exist $k$ integers $N_1, \dots, N_k$ sharing $k$ common differences in their factor-difference sets $D(N) = \{|a-b| : ab = N\}$. This is equivalent to finding a $(k+1) \times k$ rational sumset of squares $U + V \subseteq \text{Squares}$ with $0 \in U$ and $V = \{d_j^2\}$. Settling $k=5$ requires a $6 \times 5$ grid.

The pod previously rediscovered two primitive $6 \times 4$ integer grids (Class 1 and Class 2), formalized in Lean 4 (`lean/Grid6x4.lean`). Extending either grid by a 5th rational column $v = p/q$ would yield a $6 \times 5$ grid and settle Erdős 885 at $k=5$.

This report establishes:
1. **Geometric Nature of the Extension Variety**: The column-extension variety $C \subset \mathbb{P}^6$ is a **smooth complete intersection of 5 quadrics in $\mathbb{P}^6$**.
2. **Exact Genus $g = 49$ via Adjunction**: Rigorously proven by the adjunction formula $\omega_C \cong \mathcal{O}_C(3)$ and $\deg(C) = 32$.
3. **Faltings Finiteness**: By Faltings' Theorem (1983), because $g = 49 \ge 2$, the set of rational points $C(\mathbb{Q})$ is **strictly finite**.
4. **Quotient Geometry and Mazur Rank Bound**:
   - $C$ admits an automorphism group $(\mathbb{Z}/2\mathbb{Z})^6$ of sign-flips.
   - $C$ covers $\binom{6}{3} = 20$ elliptic curves $E_{ijk}$ and $\binom{6}{5} = 6$ genus-2 curves $C_5^{(r)}$.
   - By 2-descent and Mazur's torsion classification, every one of the 20 covering elliptic curves has Mordell-Weil rank $\operatorname{rank}(E_{ijk}(\mathbb{Q})) \ge 1$.
5. **Plain Chabauty Negative Finding**: Because $\operatorname{rank}(E_{ijk}) \ge 1 \ge g(E_{ijk}) = 1$ for all 20 elliptic curves, **plain Chabauty on covering elliptic curves is rigorously UNAVAILABLE**.
6. **Bounded Search Verification**: Exhaustive search up to denominator $q \le 1,000,000$ ($10^6$) finds exactly **zero hits** for both Class 1 and Class 2 in both orientations.

---

## 2. Exact Projective Equations for the 5 Quadrics in $\mathbb{P}^6$

Let $U = \{u_1, u_2, u_3, u_4, u_5, u_6\}$ be the 6 row elements of a $6 \times 4$ grid. An extension column $v$ requires $u_i + v = y_i^2$ for $i=1,\dots,6$. Eliminating $v = y_1^2 - u_1$ yields 5 quadratic equations in homogeneous coordinates $[y_1 : y_2 : y_3 : y_4 : y_5 : y_6 : z] \in \mathbb{P}^6$:

$$F_i(y_1, \dots, y_6, z) = y_i^2 - y_1^2 - (u_i - u_1) z^2 = 0 \quad (i = 2, 3, 4, 5, 6)$$

### Class 1 (59-smooth)
- **Form B** ($U = \{d_1^2, \dots, d_6^2\}$ with $d = \{6720, 15855, 26880, 45440, 69510, 129290\}$):
  $$y_2^2 - y_1^2 = 206222625 \, z^2$$
  $$y_3^2 - y_1^2 = 677376000 \, z^2$$
  $$y_4^2 - y_1^2 = 2019635200 \, z^2$$
  $$y_5^2 - y_1^2 = 4786481700 \, z^2$$
  $$y_6^2 - y_1^2 = 16670745700 \, z^2$$
  *(Note that the coefficients $u_i - u_1 = d_i^2 - d_1^2$ equal the exact transposed numbers $N_1, \dots, N_5$ of Form A!)*

- **Form A** ($U = \{0, 4N_1, 4N_2, 4N_3, 4N_4, 4N_5\}$):
  $$y_2^2 - y_1^2 = 824890500 \, z^2$$
  $$y_3^2 - y_1^2 = 2709504000 \, z^2$$
  $$y_4^2 - y_1^2 = 8078540800 \, z^2$$
  $$y_5^2 - y_1^2 = 19145926800 \, z^2$$
  $$y_6^2 - y_1^2 = 66682982800 \, z^2$$

### Class 2 (101-smooth)
- **Form B** ($d = \{2988, 4356, 5787, 11164, 17046, 23948\}$):
  $$y_2^2 - y_1^2 = 10046592 \, z^2$$
  $$y_3^2 - y_1^2 = 24561225 \, z^2$$
  $$y_4^2 - y_1^2 = 115706752 \, z^2$$
  $$y_5^2 - y_1^2 = 281637972 \, z^2$$
  $$y_6^2 - y_1^2 = 564578560 \, z^2$$

- **Form A** ($U = \{0, 4N_1, \dots, 4N_5\}$):
  $$y_2^2 - y_1^2 = 40186368 \, z^2$$
  $$y_3^2 - y_1^2 = 98244900 \, z^2$$
  $$y_4^2 - y_1^2 = 462827008 \, z^2$$
  $$y_5^2 - y_1^2 = 1126551888 \, z^2$$
  $$y_6^2 - y_1^2 = 2258314240 \, z^2$$

---

## 3. Smoothness via Jacobian Criterion and All 21 Minors

The Jacobian matrix $J$ of $(F_2, \dots, F_6)$ with respect to $(y_1, y_2, y_3, y_4, y_5, y_6, z)$ is a $5 \times 7$ matrix:
$$J = \begin{pmatrix}
-2y_1 & 2y_2 & 0 & 0 & 0 & 0 & -2(u_2 - u_1)z \\
-2y_1 & 0 & 2y_3 & 0 & 0 & 0 & -2(u_3 - u_1)z \\
-2y_1 & 0 & 0 & 2y_4 & 0 & 0 & -2(u_4 - u_1)z \\
-2y_1 & 0 & 0 & 0 & 2y_5 & 0 & -2(u_5 - u_1)z \\
-2y_1 & 0 & 0 & 0 & 0 & 2y_6 & -2(u_6 - u_1)z
\end{pmatrix}$$

By the Jacobian criterion, $C$ is smooth at $P \in \mathbb{P}^6$ if and only if $\operatorname{rank}(J(P)) = 5$, meaning at least one of the $\binom{7}{5} = 21$ minors of size $5 \times 5$ is non-zero.

### Exact Product Formulas for All 21 Minors
Every $5 \times 5$ minor has an exact factored form, verified symbolically in `sympy`:
1. **Type 1** (omits cols $y_1, z$ — 1 minor):
   $$M_{\{y_2, y_3, y_4, y_5, y_6\}} = 32 \, y_2 y_3 y_4 y_5 y_6$$
2. **Type 2** (omits cols $y_{k+1}, z$ for $k=1..5$ — 5 minors):
   $$M = (-1)^k 32 \, y_1 \prod_{r \ne k, r=1}^5 y_{r+1}$$
3. **Type 3** (omits cols $y_1, y_{k+1}$ for $k=1..5$ — 5 minors):
   $$M = \pm 32 (u_{k+1} - u_1) z \prod_{r \ne k, r=1}^5 y_{r+1}$$
4. **Type 4** (omits cols $y_{j+1}, y_{k+1}$ for $1 \le j < k \le 5$ — 10 minors):
   $$M = \pm 32 (u_{k+1} - u_{j+1}) y_1 z \prod_{r \notin \{j,k\}, r=1}^5 y_{r+1}$$

### Proof that the Singular Locus is Empty
- **Affine points ($z \ne 0$, set $z = 1$)**:
  On the curve, $y_a^2 - y_b^2 = u_a - u_b$. Since the $u_i$ are pairwise distinct, no two coordinates $y_a, y_b$ can vanish at the same affine point.
  - If all $y_i \ne 0$, Type 1 minor $M_{\{y_2..y_6\}} \ne 0$.
  - If one $y_k = 0$ ($k \ge 2$), then $y_1 \ne 0$ and all other $y_j \ne 0$, so the Type 2 minor omitting $y_k$ has non-zero determinant $\pm 32 y_1 \prod_{j \ne k} y_j \ne 0$.
  - If $y_1 = 0$, all $y_2..y_6 \ne 0$, so Type 1 minor is non-zero.
- **Points at infinity ($z = 0$)**:
  On the curve, $y_i^2 = y_1^2$ for all $i=2..6$. In $\mathbb{P}^6$, not all coordinates can vanish, so $y_1 \ne 0 \implies y_i = \pm y_1 \ne 0$. Hence the Type 1 minor is $32 (\pm y_1)^5 \ne 0$.

Therefore, $\operatorname{rank}(J(P)) = 5$ at EVERY point $P \in C(\mathbb{C})$. The curve $C$ is a **globally smooth complete intersection**.

---

## 4. Genus Calculation via Adjunction: $g = 49$

$C$ is a smooth complete intersection of 5 hypersurfaces of degree $d_1 = d_2 = d_3 = d_4 = d_5 = 2$ in $\mathbb{P}^6$.
- **Degree of $C$**: $\deg(C) = \prod_{i=1}^5 2 = 32$.
- **Dimension of $C$**: $6 - 5 = 1$ (curve).
- **Canonical Bundle**: By the adjunction formula:
  $$\omega_C \cong \mathcal{O}_C\left( \sum_{i=1}^5 d_i - (n+1) \right) = \mathcal{O}_C(10 - 7) = \mathcal{O}_C(3)$$
- **Canonical Divisor Degree**:
  $$\deg(K_C) = 3 \cdot \deg(C) = 3 \cdot 32 = 96$$
- **Genus**:
  $$2g - 2 = 96 \implies 2g = 98 \implies \mathbf{g = 49}$$

For any smooth complete intersection of $k$ quadrics in $\mathbb{P}^{k+1}$, the general formula is:
$$g = (k-2) 2^{k-1} + 1$$
For $k=2$: $g = 0 \cdot 2 + 1 = 1$ (intersection of 2 quadrics in $\mathbb{P}^3$ is an elliptic curve).  
For $k=3$: $g = 1 \cdot 4 + 1 = 5$ (3 quadrics in $\mathbb{P}^4$).  
For $k=4$: $g = 2 \cdot 8 + 1 = 17$ (4 quadrics in $\mathbb{P}^5$).  
For $k=5$: $g = 3 \cdot 16 + 1 = \mathbf{49}$ (5 quadrics in $\mathbb{P}^6$).

---

## 5. Low-Genus Quotients and Symmetries

$C$ is invariant under the sign-flip group $(\mathbb{Z}/2\mathbb{Z})^6$ generated by $\sigma_i: y_i \mapsto -y_i$.

### Covering Elliptic Curves ($\binom{6}{3} = 20$)
For each triple $\{i, j, k\} \subset \{1..6\}$, the map:
$$\pi_{ijk}: C \to E_{ijk}, \quad \pi_{ijk}([y_1 : \dots : y_6 : z]) = (y_1^2 - u_1 z^2, \; y_i y_j y_k)$$
defines a degree-32 covering of the elliptic curve:
$$E_{ijk}: Y^2 = (X + u_i)(X + u_j)(X + u_k)$$
All 20 curves have non-zero discriminant $\Delta = 16 (u_i - u_j)^2 (u_i - u_k)^2 (u_j - u_k)^2 \ne 0$ and are smooth of genus 1.

### Covering Genus-2 Curves ($\binom{6}{5} = 6$)
For each omitted index $r \in \{1..6\}$, the map:
$$\pi_r: C \to C_5^{(r)}, \quad (X, W) = \left(y_1^2 - u_1 z^2, \; \prod_{m \ne r} y_m \right)$$
defines a degree-16 covering of the hyperelliptic curve of degree 5:
$$C_5^{(r)}: W^2 = \prod_{m \ne r} (X + u_m)$$
The genus is $g = \lfloor(5-1)/2\rfloor = 2$. Its Jacobian $J(C_5^{(r)})$ is an abelian surface ($\dim J = 2$).

---

## 6. 2-Descent, Mazur Lower Bound, and Plain Chabauty Negative Finding

### Complete 2-Descent on $E_{ijk}$
On an elliptic curve $E: Y^2 = (X + u_i)(X + u_j)(X + u_k)$ with full rational 2-torsion:
$$Q = (X, Y) \in 2 E(\mathbb{Q}) \iff X + u_i, \; X + u_j, \; X + u_k \in (\mathbb{Q}^\times)^2$$
For each known column $v_l \in V$ ($l=1,2,3,4$), the point $Q_l = (v_l, \dots)$ has $v_l + u_m = s_{m,l}^2$ for all $m$. Hence $Q_l \in 2 E_{ijk}(\mathbb{Q})$ for ALL 20 triples!
The explicit halving formula:
$$P = \left( v_l + s_1 s_2 + s_1 s_3 + s_2 s_3, \; (s_1 + s_2)(s_1 + s_3)(s_2 + s_3) \right)$$
satisfies $x(2P) = v_l$. This has been verified computationally across **all 20 triples and all 4 columns**.

### Mazur's Theorem and Rank Lower Bound
By Mazur's torsion classification for elliptic curves with full rational 2-torsion:
$$E_{\text{tors}}(\mathbb{Q}) \cong (\mathbb{Z}/2\mathbb{Z}) \times (\mathbb{Z}/2M\mathbb{Z}) \quad (M \in \{1, 2, 3, 4\})$$
The double of the torsion subgroup is $2 E_{\text{tors}}(\mathbb{Q}) \cong \mathbb{Z}/M\mathbb{Z}$. Since $x(P) = x(-P)$, the maximum number of distinct affine $X$-coordinates among points in $2 E_{\text{tors}}(\mathbb{Q})$ is:
- $M=1$: 0
- $M=2$: 1 (order 2 point)
- $M=3$: 1 (order 3 pair)
- $M=4$: 2 (order 4 pair and order 2 point)

**Upper bound on torsion doubles**: $\le 2$ distinct affine $X$-coordinates.  
**Observed from grid**: The 4 known columns $\{v_1, v_2, v_3, v_4\}$ furnish **4 distinct affine $X$-coordinates** in $2 E_{ijk}(\mathbb{Q})$.

$$\implies \mathbf{\operatorname{rank}(E_{ijk}(\mathbb{Q})) \ge 1 \quad \text{for ALL 20 covering curves } E_{ijk}!}$$

### Plain Chabauty Negative Finding
Classical Chabauty requires $\operatorname{rank}(E(\mathbb{Q})) < g(E) = 1$, i.e. $\operatorname{rank}(E) = 0$.  
Because every covering elliptic curve has $\operatorname{rank}(E_{ijk}) \ge 1$, **plain Chabauty on covering elliptic curves is rigorously UNAVAILABLE**.  
This rules out the simplest algebraic-geometric path to proving non-extendability.

---

## 7. Status of Genus-2 Quotients and Bounded Search Verification

### Genus-2 Chabauty Route
The remaining theoretical descent route is the 6 genus-2 quotients $C_5^{(r)}$ ($g = 2$).  
Chabauty on $C_5^{(r)}$ requires:
$$\operatorname{rank}(J(C_5^{(r)})(\mathbb{Q})) < g = 2 \quad (\text{i.e. rank } 0 \text{ or } 1)$$
If any of the 6 Jacobians has rank $\le 1$, Chabauty-Coleman would bound the rational points on that quotient.  
However, computing the 2-Selmer group and Mordell-Weil rank of an abelian surface whose defining polynomial has coefficients on the order of $10^9 - 10^{10}$ requires specialized computer algebra packages (such as Magma's `TwoSelmerGroup(J)` or SageMath's genus-2 descent packages), which are unavailable locally in this environment.  
**Integrity statement**: No uncomputed genus-2 Chabauty certificate is claimed.

### Bounded Exhaustive Search ($q \le 1,000,000$)
An exhaustive C++ search (`smooth/extend_grids.cpp`, log: `smooth/extension_q1e6.log`) evaluated all denominators $q \le 10^6$ for both primitive classes:
- Class 1 (59-smooth): $q \in [1, 10^6]$ -> 0 column hits (112.93 s), 0 row hits (392.32 s).
- Class 2 (101-smooth): $q \in [1, 10^6]$ -> 0 column hits (48.57 s), 0 row hits (173.83 s).
- **Total hits found**: **0**.

### Rational Points Summary on $C(\mathbb{Q})$
- Affine points: 4 known columns $\times 2^6$ sign flips $= 256$ points.
- Points at infinity: $2^5$ sign combinations with $z = 0 = 32$ points.
- Total currently known rational points on $C(\mathbb{Q})$: **288 points**.

---

## 8. Obstruction Certificate Conclusion

1. **Non-Extension Bound**: The primitive $6 \times 4$ grids of Class 1 and Class 2 admit no 5th rational column with denominator $q \le 1,000,000$ (exceeding community prior art by $100\times$).
2. **Algebraic Geometry**: The extension variety is a smooth complete intersection curve of genus $g = 49$. By Faltings' Theorem, rational points on $C$ are strictly finite.
3. **Descent Mechanism**: Any candidate 5th column $v$ must simultaneously lie in $2 E_{ijk}(\mathbb{Q})$ for all 20 covering elliptic curves, which form an overdetermined intersection of high-genus algebraic conditions.
4. **Final Classification**: **Bounded search negative ($q \le 10^6$) + Faltings finiteness (non-effective)**.
