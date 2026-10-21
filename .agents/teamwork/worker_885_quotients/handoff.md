# Handoff Report: Algebraic Geometry of Column Extension for Erdős 885 $6 \times 4$ Grids

**Author**: `worker_885_quotients`  
**Working Directory**: `/Users/mike/dev/ctrl/.agents/teamwork/worker_885_quotients`  
**Target Files**:
- `/Users/mike/dev/ctrl/tools/verify_885_geometry.py`
- `/Users/mike/dev/ctrl/work/pod/885/OBSTRUCTION.md`
- `/Users/mike/dev/ctrl/tests/test_885_geometry.py`

---

## 1. Observation

1. **Grid Configurations & Duality**:
   - Class 1 (59-smooth): Form B has 3 integers sharing 6 differences $d = \{6720, 15855, 26880, 45440, 69510, 129290\}$. Form A has 5 integers $N = \{206222625, 677376000, 2019635200, 4786481700, 16670745700\}$ sharing 4 differences $d = \{13440, 75936, 129360, 279840\}$.
   - Class 2 (101-smooth): Form B has 3 integers sharing 6 differences $d = \{2988, 4356, 5787, 11164, 17046, 23948\}$. Form A has 5 integers $N = \{10046592, 24561225, 115706752, 281637972, 564578560\}$ sharing 4 differences $d = \{5976, 10104, 24216, 69624\}$.
   - In Form B, the coefficients $\Delta u_i = d_i^2 - d_1^2$ equal the exact transposed integers $N_{i-1}$ of Form A. In Form A, $\Delta u_i = 4 N_{i-1}$. All 24 sums $u_i + v_j$ are exact integer squares in all 4 configurations (`test_grid_square_sums_class1_and_class2`).

2. **Projective Equations in $\mathbb{P}^6$**:
   Homogeneous coordinates $[y_1 : y_2 : y_3 : y_4 : y_5 : y_6 : z]$ with 5 quadrics:
   $$F_i = y_i^2 - y_1^2 - (u_i - u_1) z^2 = 0 \quad (i = 2, 3, 4, 5, 6)$$
   For Class 1 Form B:
   - $y_2^2 - y_1^2 = 206222625 \, z^2$
   - $y_3^2 - y_1^2 = 677376000 \, z^2$
   - $y_4^2 - y_1^2 = 2019635200 \, z^2$
   - $y_5^2 - y_1^2 = 4786481700 \, z^2$
   - $y_6^2 - y_1^2 = 16670745700 \, z^2$

3. **Symbolic Verification of the 21 Jacobian Minors**:
   In `tools/verify_885_geometry.py:146-210`, sympy computes the determinants of all $\binom{7}{5} = 21$ submatrices of size $5 \times 5$ from the $5 \times 7$ Jacobian matrix. All 21 match the exact factored product formulas:
   - Type 1 (1 minor, omits $y_1, z$): $32 \prod_{r=2}^6 y_r$.
   - Type 2 (5 minors, omits $y_{k+1}, z$): $(-1)^k 32 y_1 \prod_{r \ne k, r \ge 2} y_r$.
   - Type 3 (5 minors, omits $y_1, y_{k+1}$): $\pm 32 (u_{k+1} - u_1) z \prod_{r \ne k, r \ge 2} y_r$.
   - Type 4 (10 minors, omits $y_{j+1}, y_{k+1}$): $\pm 32 (u_{k+1} - u_{j+1}) y_1 z \prod_{r \notin \{j,k\}, r \ge 2} y_r$.
   Command output: `Jacobian 5x5 minors verified symbolically (all 21 via sympy): True`.

4. **Smoothness Proof (Nullstellensatz)**:
   - On $z = 1$: $y_a^2 - y_b^2 = u_a - u_b \ne 0 \implies$ at most one $y_k$ can vanish. If one vanishes, the swapped Type 2 minor is non-zero. If none vanish, Type 1 is non-zero.
   - On $z = 0$: $y_i^2 = y_1^2 \ne 0 \implies$ no $y_i$ can vanish, so Type 1 minor is non-zero.
   - Singular locus $\operatorname{Sing}(C) = \emptyset$.

5. **Adjunction Formula & Genus**:
   - $\omega_C \cong \mathcal{O}_C(\sum_{i=1}^5 2 - (6+1)) = \mathcal{O}_C(10 - 7) = \mathcal{O}_C(3)$.
   - $\deg(C) = 2^5 = 32$.
   - $\deg(K_C) = 3 \times 32 = 96 = 2g - 2 \implies 2g = 98 \implies \mathbf{g = 49}$.
   - For complete intersection of $k$ quadrics in $\mathbb{P}^{k+1}$, $g = (k-2)2^{k-1} + 1$, confirming $g=49$ for $k=5$.

6. **2-Descent & Mazur Rank Lower Bound Across All 20 Curves**:
   - `verify_mazur_rank_lower_bound_all_20_curves` iterates over ALL 20 triples $\{i, j, k\} \subset \{0..5\}$.
   - For all 20 triples and all 4 known columns $v_l \in V$, the halved point $P = (v_l + s_1 s_2 + s_1 s_3 + s_2 s_3, (s_1+s_2)(s_1+s_3)(s_2+s_3))$ doubles to $x(2P) = v_l$.
   - Thus $2 E_{ijk}(\mathbb{Q})$ contains 4 distinct affine $X$-coordinates.
   - Under Mazur's classification, for full rational 2-torsion $E_{\text{tors}}(\mathbb{Q}) \cong \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2M\mathbb{Z}$ ($M \le 4$), $2 E_{\text{tors}}(\mathbb{Q}) \cong \mathbb{Z}/M\mathbb{Z}$ has at most 2 distinct affine $X$-coordinates.
   - Since $4 > 2$, $\operatorname{rank}(E_{ijk}(\mathbb{Q})) \ge 1$ for ALL 20 curves.

7. **Negative Finding on Plain Chabauty**:
   - Plain Chabauty on an elliptic curve $E$ requires $\operatorname{rank}(E(\mathbb{Q})) < g(E) = 1$, i.e., rank 0.
   - Because $\operatorname{rank}(E_{ijk}) \ge 1$ for all 20 curves, plain Chabauty on $E_{ijk}$ is UNAVAILABLE.

8. **Bounded Exhaustive Search**:
   - `smooth/extension_q1e6_coverage.txt` confirms:
     Class 1: $q \le 1,000,000$ column_hits = 0, row_hits = 0.
     Class 2: $q \le 1,000,000$ column_hits = 0, row_hits = 0.

---

## 2. Logic Chain

1. **Existence of Extension $\iff$ Rational Points on $C$**:
   A 5th column $v = p/q$ exists for a $6 \times 4$ grid if and only if there exists an affine rational point $[y_1 : \dots : y_6 : 1] \in C(\mathbb{Q})$ with $y_1^2 - u_1 = v \notin \{v_1, v_2, v_3, v_4\}$.
2. **Dimension and Smoothness**:
   By the Jacobian criterion, because all 6 entries in $U$ are distinct, the $5 \times 7$ Jacobian matrix has rank 5 everywhere on $C(\mathbb{C})$. Thus $C$ is a smooth projective variety of dimension $6 - 5 = 1$ (a non-singular projective curve) and degree $2^5 = 32$.
3. **Genus 49 via Adjunction**:
   The canonical bundle is $\omega_C \cong \mathcal{O}_C(3)$, giving canonical degree $\deg(K_C) = 3 \times 32 = 96$. By $2g - 2 = 96$, the curve has genus $g = 49$.
4. **Faltings Finiteness**:
   By Faltings' Theorem (Mordell Conjecture, 1983), any smooth projective curve of genus $g \ge 2$ over $\mathbb{Q}$ has only finitely many rational points. Therefore, $C(\mathbb{Q})$ is strictly finite. Currently, 288 rational points are known (256 affine points from the 4 known columns under $(\mathbb{Z}/2\mathbb{Z})^6$, plus 32 points at infinity).
5. **Obstruction via Low-Genus Quotients**:
   - Projecting to any of the 20 covering elliptic curves $E_{ijk}: Y^2 = (X+u_i)(X+u_j)(X+u_k)$ requires $v \in x(2 E_{ijk}(\mathbb{Q}))$.
   - Because the 4 known columns provide 4 distinct affine points in $2 E_{ijk}(\mathbb{Q})$, Mazur's torsion classification forces $\operatorname{rank}(E_{ijk}(\mathbb{Q})) \ge 1$ for all 20 curves.
   - Consequently, plain Chabauty cannot apply to any of the 20 elliptic curves ($r \ge g$).
6. **Genus-2 Quotients and Theoretical Route**:
   - $C$ also covers 6 genus-2 hyperelliptic curves $C_5^{(r)}: W^2 = \prod_{m \ne r} (X+u_m)$.
   - An algebraic Chabauty obstruction would require bounding $\operatorname{rank}(J(C_5^{(r)})(\mathbb{Q})) < 2$. Computing 2-Selmer ranks of these abelian surfaces with $10^9$-scale coefficients requires Magma or Sage, unavailable locally.
7. **Synthesis**:
   The non-existence of a 5th column is established computationally for all denominators $q \le 10^6$ (0 hits). Faltings' theorem guarantees that rational points cannot form an infinite family.

---

## 3. Caveats

1. **Unconditional Global Obstruction**: Faltings' theorem guarantees finiteness of $C(\mathbb{Q})$, but is non-effective (it does not provide an explicit height bound). An unconditional proof that $C(\mathbb{Q})$ contains *only* the 288 known rational points would require either:
   - Chabauty-Coleman on one of the 6 genus-2 quotients $C_5^{(r)}$ (requiring $\operatorname{rank}(J) \le 1$), or
   - An explicit Mordell-Weil sieve across multiple primes proving non-solvability of the 2-cover intersection.
   Neither calculation can be completed with local Python standard tools.
2. **Search Depth**: The non-extension result is exhaustive up to $q \le 1,000,000$. Columns with denominator $q > 10^6$ are not ruled out by the numerical search alone.
3. **Scope**: The analysis applies specifically to the known primitive Class 1 and Class 2 configurations (and their transposes). It does not rule out the existence of $6 \times 5$ grids from an entirely different, undiscovered family.

---

## 4. Conclusion

1. **Geometric Identity**: The column-extension variety for the known $6 \times 4$ grids is rigorously proved to be a smooth complete intersection of 5 quadrics in $\mathbb{P}^6$ of genus $g = 49$.
2. **Honest Classification**: The obstruction status is certified as:
   **Bounded search negative ($q \le 10^6$) + Faltings finiteness (non-effective)**.
3. **Negative Result on Plain Chabauty**: We prove that all 20 covering elliptic curves $E_{ijk}$ have Mordell-Weil rank $\ge 1$, proving that plain Chabauty cannot succeed on any elliptic quotient.
4. **All Deliverables Completed**:
   - `tools/verify_885_geometry.py` executes exact symbolic verification and geometric calculations.
   - `work/pod/885/OBSTRUCTION.md` provides the full certificate and mathematical treatise.
   - `tests/test_885_geometry.py` provides 13 passing unit tests with 100% clean lint.

---

## 5. Verification Method

1. **Run the Geometric Verification Tool**:
   ```bash
   uv run python tools/verify_885_geometry.py
   ```
   *Expected output*: Exits 0, confirms grid square-sums, displays exact quadrics, reports all 21 minors verified symbolically via sympy, confirms smooth complete intersection, reports adjunction genus $g = 49$, confirms Mazur rank bound $\ge 1$ across all 20 triples, and outputs honest classification.

2. **Run Unit Tests**:
   ```bash
   uv run pytest -v tests/test_885_geometry.py
   ```
   *Expected output*: 13 passed in $< 4$ seconds.

3. **Run Ruff Lint Check**:
   ```bash
   uv run ruff check tools/verify_885_geometry.py tests/test_885_geometry.py
   ```
   *Expected output*: `All checks passed!`

4. **Inspect Obstruction Certificate**:
   ```bash
   cat work/pod/885/OBSTRUCTION.md
   ```
