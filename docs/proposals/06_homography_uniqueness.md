# Four-Point Planar Homography Uniqueness and Projective Frame Rigidity in Lean 4

**Author**: Mike Helsel  
**Date**: October 18, 2026  
**Status**: Machine-Checked & Verified (`ControlsLean.Vision.HomographyUniqueness`)  
**Target Repository**: `ctrl` (`ControlsLean/Vision/HomographyUniqueness.lean`)  
**Axiom Footprint**: Standard Lean 4 axioms only (`[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero custom axioms)

---

## 1. Abstract

We formalize the fundamental four-point uniqueness and projective frame rigidity theorems of planar projective geometry ($\mathbb{P}^2(K)$) in Lean 4 (`ControlsLean.Vision.HomographyUniqueness`). In geometric computer vision and classical algebraic projective geometry (Hartley & Zisserman, 2004, Theorem 2.10 & Section 4.1; Semple & Kneebone, 1952, Chapter IV), a planar homography (projective collineation) is represented by a non-singular $3 \times 3$ matrix $H \in \mathrm{GL}(3, K)$ acting on homogeneous ray coordinates up to non-zero scalar equivalence, yielding $9 - 1 = 8$ degrees of freedom in $\mathrm{PGL}(3, K)$. Because each point-to-point projective correspondence $x'_i \propto H x_i$ eliminates two degrees of freedom, four point correspondences in general position (no three collinear) uniquely determine $H$ up to a single global homogeneous scalar factor.

We provide machine-checked proofs over any commutative ring / field $K$ establishing:
1. **Standard Projective Frame General Position**: The canonical projective basis $e_0 = [1,0,0]^\top$, $e_1 = [0,1,0]^\top$, $e_2 = [0,0,1]^\top$, and unit point $e_3 = [1,1,1]^\top$ satisfy $e_0 + e_1 + e_2 = e_3$ and every 3-point subset has determinant $\pm 1$.
2. **Diagonal Reduction from Three Basis Points (`eq_diagonal_of_fixes_basis`, `homography_Arena_diagonal`)**: Any $H \in M_3(K)$ that fixes the three coordinate vertices $e_0, e_1, e_2$ up to scalars $\lambda_0, \lambda_1, \lambda_2$ ($H e_i = \lambda_i e_i$) is necessarily the diagonal matrix $\mathrm{diag}(\lambda_0, \lambda_1, \lambda_2)$.
3. **Scalar Matrix Rigidity on the Four-Point Canonical Frame (`eq_smul_one_of_fixes_canonical_frame`)**: If $H$ fixes $e_0, e_1, e_2$ up to $\lambda_0, \lambda_1, \lambda_2$ and additionally fixes the fourth unit point $e_3 = [1,1,1]^\top$ up to $\lambda_3$ ($H e_3 = \lambda_3 e_3$), then all four projective scale factors collapse to a single scalar ($\lambda_0 = \lambda_1 = \lambda_2 = \lambda_3$) and $H = \lambda_3 I_3$.
4. **Canonical Frame Homography Uniqueness (`homography_unique_on_canonical_frame`)**: If two homographies $H_1, H_2 \in M_3(K)$ (with $H_2$ invertible) agree projectively on $e_0, e_1, e_2, e_3$ ($H_1 e_i = \lambda_i H_2 e_i$), then $\lambda_0 = \lambda_1 = \lambda_2 = \lambda_3$ and $H_1 = \lambda_3 H_2$.
5. **General Four-Point Projective Frame Rigidity (`homography_unique_four_points`, `two_homographies_eq_smul_of_four_points`, `homography_rigidity_of_general_position`)**: For any 4-point projective frame $(p_0, p_1, p_2, p_3)$ in general position (formulated both via an invertible basis change $B$ with $p_i = B e_i$ and via an explicit general-position decomposition $p_3 = c_0 p_0 + c_1 p_1 + c_2 p_2$), fixing the four rays forces $H = \lambda_3 I_3$, and any two homographies mapping $(p_0, p_1, p_2, p_3)$ to the same projective rays satisfy $H_1 = \lambda_3 H_2$.

---

## 2. Mathematical Formulation

### 2.1 The Canonical Projective Frame in $\mathbb{P}^2(K)$

Let $K$ be a commutative ring (or field). Homogeneous coordinates in the projective plane $\mathbb{P}^2(K)$ are represented by vectors $x \in K^3 \setminus \{0\}$ up to scalar multiplication $x \sim \lambda x$ ($\lambda \in K^\times$). While three non-collinear points span the vector space $K^3$, they do not uniquely fix a projective coordinate system because any non-singular diagonal matrix $\mathrm{diag}(\lambda_0, \lambda_1, \lambda_2)$ with distinct $\lambda_i$ preserves the three coordinate axes while distorting cross-ratios and general rays.

A **projective frame** (or **projective basis**) of $\mathbb{P}^2(K)$ therefore requires **four** points in general position (no three collinear). The **canonical projective frame** consists of the three standard basis vectors together with the unit point:
$$e_0 = \begin{bmatrix} 1 \\ 0 \\ 0 \end{bmatrix}, \quad e_1 = \begin{bmatrix} 0 \\ 1 \\ 0 \end{bmatrix}, \quad e_2 = \begin{bmatrix} 0 \\ 0 \\ 1 \end{bmatrix}, \quad e_3 = \begin{bmatrix} 1 \\ 1 \\ 1 \end{bmatrix} = e_0 + e_1 + e_2.$$

Every 3-point sub-configuration is non-collinear:
$$\det[e_0, e_1, e_2] = 1, \quad \det[e_0, e_1, e_3] = 1, \quad \det[e_0, e_2, e_3] = -1, \quad \det[e_1, e_2, e_3] = 1.$$

### 2.2 Three-Point Diagonal Reduction and Four-Point Scalar Rigidity

**Lemma 1 (Diagonal Reduction from Three Basis Points).** Let $H \in M_3(K)$ satisfy:
$$H e_i = \lambda_i e_i \qquad \text{for } i \in \{0, 1, 2\}.$$
Since $H e_j$ is the $j$-th column of $H$, the $j$-th column of $H$ equals $\lambda_j e_j$, which immediately implies:
$$H = \mathrm{diag}(\lambda_0, \lambda_1, \lambda_2) = \begin{bmatrix} \lambda_0 & 0 & 0 \\ 0 & \lambda_1 & 0 \\ 0 & 0 & \lambda_2 \end{bmatrix}.$$

**Theorem 2 (Four-Point Canonical Frame Rigidity).** Suppose $H \in M_3(K)$ fixes all four canonical frame points up to scalars $\lambda_0, \lambda_1, \lambda_2, \lambda_3 \in K$:
$$H e_0 = \lambda_0 e_0, \quad H e_1 = \lambda_1 e_1, \quad H e_2 = \lambda_2 e_2, \quad H e_3 = \lambda_3 e_3.$$
By linearity of matrix-vector multiplication and $e_3 = e_0 + e_1 + e_2$:
$$\begin{bmatrix} \lambda_3 \\ \lambda_3 \\ \lambda_3 \end{bmatrix} = \lambda_3 e_3 = H e_3 = H(e_0 + e_1 + e_2) = \lambda_0 e_0 + \lambda_1 e_1 + \lambda_2 e_2 = \begin{bmatrix} \lambda_0 \\ \lambda_1 \\ \lambda_2 \end{bmatrix}.$$
Comparing components yields $\lambda_0 = \lambda_1 = \lambda_2 = \lambda_3$, and substituting into Lemma 1 gives:
$$H = \mathrm{diag}(\lambda_3, \lambda_3, \lambda_3) = \lambda_3 I_3.$$

### 2.3 Change of Projective Frame and General Four-Point Uniqueness

Let $(p_0, p_1, p_2, p_3)$ be an arbitrary four-point projective frame in $K^3$. By general position, $(p_0, p_1, p_2)$ forms a basis of $K^3$ and $p_3$ can be uniquely decomposed as:
$$p_3 = c_0 p_0 + c_1 p_1 + c_2 p_2$$
with non-zero coefficients $c_0, c_1, c_2 \in K^\times$ (if any $c_i = 0$, $p_3$ would be collinear with the other two basis points, violating general position). Defining the frame basis matrix:
$$B = \begin{bmatrix} c_0 p_0 & c_1 p_1 & c_2 p_2 \end{bmatrix} \in \mathrm{GL}(3, K),$$
we have:
$$B e_0 = c_0 p_0, \quad B e_1 = c_1 p_1, \quad B e_2 = c_2 p_2, \quad B e_3 = B(e_0 + e_1 + e_2) = c_0 p_0 + c_1 p_1 + c_2 p_2 = p_3,$$
and $\det(B) = c_0 c_1 c_2 \det[p_0, p_1, p_2] \neq 0$.

**Theorem 3 (General Four-Point Projective Frame Rigidity — Hartley & Zisserman Theorem 2.10).**
Suppose $H \in M_3(K)$ fixes the four points $p_i = B e_i$ ($i=0,1,2,3$) of a projective frame up to scalars $\lambda_0, \lambda_1, \lambda_2, \lambda_3$:
$$H p_i = \lambda_i p_i \qquad (i = 0, 1, 2, 3).$$
Then the conjugated matrix $M = B^{-1} H B$ satisfies:
$$M e_i = B^{-1} H (B e_i) = B^{-1} (\lambda_i B e_i) = \lambda_i e_i \qquad (i = 0, 1, 2, 3).$$
By Theorem 2, $\lambda_0 = \lambda_1 = \lambda_2 = \lambda_3$ and $M = \lambda_3 I_3$, whence:
$$H = B M B^{-1} = B (\lambda_3 I_3) B^{-1} = \lambda_3 I_3.$$

**Corollary 4 (Uniqueness of Planar Homography from Four Point Correspondences).**
Let $H_1, H_2 \in M_3(K)$ with $H_2$ invertible ($H_2^{-1} H_2 = I_3$). If $H_1$ and $H_2$ map four points $p_i = B e_i$ ($i=0,1,2,3$) in general position to the same projective rays:
$$H_1 p_i = \lambda_i H_2 p_i \qquad (i = 0, 1, 2, 3),$$
then applying $H_2^{-1}$ on the left shows that $(H_2^{-1} H_1) p_i = \lambda_i p_i$. By Theorem 3, $\lambda_0 = \lambda_1 = \lambda_2 = \lambda_3$ and $H_2^{-1} H_1 = \lambda_3 I_3$, so:
$$H_1 = \lambda_3 H_2.$$
Thus, a planar homography is uniquely determined up to a single global scale factor by four point correspondences in general position (the theoretical foundation of the 4-point Direct Linear Transformation / DLT algorithm).

---

## 3. Formalization Architecture in Lean 4

The module `ControlsLean/Vision/HomographyUniqueness.lean` builds directly upon `ControlsLean.Vision.Homography` and `Mathlib.Data.Matrix.Diagonal` / `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`.

### 3.1 Key Design Decisions
1. **Commutative Ring Generality**:
   All core canonical-frame and basis-conjugation theorems (`eq_diagonal_of_fixes_basis`, `homography_Arena_diagonal`, `eq_smul_one_of_fixes_canonical_frame`, `homography_unique_on_canonical_frame`, `homography_unique_four_points`, `two_homographies_eq_smul_of_four_points`) are proved over an arbitrary `[CommRing K]` without requiring division. Division-free explicit inverse witnesses (`H₂_inv * H₂ = 1`, `B_inv * B = 1`) are combined with Mathlib's `mul_eq_one_comm` (`H₂_inv * H₂ = 1 ↔ H₂ * H₂_inv = 1`) so that left-invertibility automatically yields two-sided invertibility over any commutative ring.
2. **Simultaneous Scalar Equality and Matrix Identity**:
   Rather than proving only $H = \lambda_3 \cdot 1$, our headline theorems return the conjunction `(λ₀ = λ₃ ∧ λ₁ = λ₃ ∧ λ₂ = λ₃) ∧ H = λ₃ • 1` (and similarly `H₁ = λ₃ • H₂`), certifying both that the individual projective depth/ray scale factors must coincide and that the matrix is globally scaled.
3. **Explicit Frame Basis Matrix Construction (`frameBasisMatrix`)**:
   In addition to the change-of-basis formulation $p_i = B e_i$, we formalize the explicit matrix `frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂` whose columns are $c_0 p_0, c_1 p_1, c_2 p_2$, prove its action on $e_0, e_1, e_2, e_3$, prove the determinant factorization $\det(B) = c_0 c_1 c_2 \det[p_0, p_1, p_2]$, and deduce `homography_rigidity_of_general_position` directly for unscaled points $p_0, p_1, p_2, p_3$.

### 3.2 Formal Lean 4 Declarations

```lean
/-- Standard projective frame points in `Fin 3 → K`. -/
def e₀ : Fin 3 → K := ![1, 0, 0]
def e₁ : Fin 3 → K := ![0, 1, 0]
def e₂ : Fin 3 → K := ![0, 0, 1]
def e₃ : Fin 3 → K := ![1, 1, 1]

/-- Diagonal Scaling from 3 Basis Points. -/
theorem eq_diagonal_of_fixes_basis (H : Matrix (Fin 3) (Fin 3) K) (s : Fin 3 → K)
    (h₀ : H *ᵥ e₀ = s 0 • e₀)
    (h₁ : H *ᵥ e₁ = s 1 • e₁)
    (h₂ : H *ᵥ e₂ = s 2 • e₂) :
    H = Matrix.diagonal s

/-- Indexed-family formulation of Diagonal Scaling from 3 Basis Points. -/
theorem homography_Arena_diagonal (H : Matrix (Fin 3) (Fin 3) K) (s : Fin 3 → K)
    (h : ∀ i : Fin 3, H *ᵥ stdBasis i = s i • stdBasis i) :
    H = Matrix.diagonal s

/-- Scalar Matrix from 4 Canonical Frame Points. -/
theorem eq_smul_one_of_fixes_canonical_frame (H : Matrix (Fin 3) (Fin 3) K)
    (s₀ s₁ s₂ s₃ : K)
    (h₀ : H *ᵥ e₀ = s₀ • e₀)
    (h₁ : H *ᵥ e₁ = s₁ • e₁)
    (h₂ : H *ᵥ e₂ = s₂ • e₂)
    (h₃ : H *ᵥ e₃ = s₃ • e₃) :
    (s₀ = s₃ ∧ s₁ = s₃ ∧ s₂ = s₃) ∧ H = s₃ • (1 : Matrix (Fin 3) (Fin 3) K)

/-- Uniqueness of Homographies on the Canonical Frame. -/
theorem homography_unique_on_canonical_frame (H₁ H₂ H₂_inv : Matrix (Fin 3) (Fin 3) K)
    (hinv : H₂_inv * H₂ = 1)
    (s₀ s₁ s₂ s₃ : K)
    (h₀ : H₁ *ᵥ e₀ = s₀ • (H₂ *ᵥ e₀))
    (h₁ : H₁ *ᵥ e₁ = s₁ • (H₂ *ᵥ e₁))
    (h₂ : H₁ *ᵥ e₂ = s₂ • (H₂ *ᵥ e₂))
    (h₃ : H₁ *ᵥ e₃ = s₃ • (H₂ *ᵥ e₃)) :
    (s₀ = s₃ ∧ s₁ = s₃ ∧ s₂ = s₃) ∧ H₁ = s₃ • H₂

/-- General Four-Point Projective Frame Rigidity (Hartley & Zisserman Theorem 2.10). -/
theorem homography_unique_four_points (H B B_inv : Matrix (Fin 3) (Fin 3) K)
    (hB : B_inv * B = 1)
    (s₀ s₁ s₂ s₃ : K)
    (h₀ : H *ᵥ (B *ᵥ e₀) = s₀ • (B *ᵥ e₀))
    (h₁ : H *ᵥ (B *ᵥ e₁) = s₁ • (B *ᵥ e₁))
    (h₂ : H *ᵥ (B *ᵥ e₂) = s₂ • (B *ᵥ e₂))
    (h₃ : H *ᵥ (B *ᵥ e₃) = s₃ • (B *ᵥ e₃)) :
    (s₀ = s₃ ∧ s₁ = s₃ ∧ s₂ = s₃) ∧ H = s₃ • (1 : Matrix (Fin 3) (Fin 3) K)

/-- Two Homographies Agreeing on a General Four-Point Projective Frame. -/
theorem two_homographies_eq_smul_of_four_points (H₁ H₂ H₂_inv B B_inv : Matrix (Fin 3) (Fin 3) K)
    (hinv : H₂_inv * H₂ = 1) (hB : B_inv * B = 1)
    (s₀ s₁ s₂ s₃ : K)
    (h₀ : H₁ *ᵥ (B *ᵥ e₀) = s₀ • (H₂ *ᵥ (B *ᵥ e₀)))
    (h₁ : H₁ *ᵥ (B *ᵥ e₁) = s₁ • (H₂ *ᵥ (B *ᵥ e₁)))
    (h₂ : H₁ *ᵥ (B *ᵥ e₂) = s₂ • (H₂ *ᵥ (B *ᵥ e₂)))
    (h₃ : H₁ *ᵥ (B *ᵥ e₃) = s₃ • (H₂ *ᵥ (B *ᵥ e₃))) :
    (s₀ = s₃ ∧ s₁ = s₃ ∧ s₂ = s₃) ∧ H₁ = s₃ • H₂
```

---

## 4. Literature Grounding & Citations

1. **Hartley, R., & Zisserman, A.** (2004). *Multiple View Geometry in Computer Vision* (2nd ed.). Cambridge University Press.
   - **Theorem 2.10 (Unique homography from four points in general position)**, p. 34, and **Section 4.1 (The Direct Linear Transformation — DLT algorithm)**, pp. 88–91:
     *Statement*: A projective transformation of $\mathbb{P}^2$ is uniquely determined up to scale by the images of four points in general position (no three of which are collinear). Specifically, if a projectivity fixes four points in general position, it is a scalar multiple of the identity matrix.
     *Formalization*: `eq_smul_one_of_fixes_canonical_frame`, `homography_unique_on_canonical_frame`, `homography_unique_four_points`, `two_homographies_eq_smul_of_four_points`, and `homography_rigidity_of_general_position`.

2. **Semple, J. G., & Kneebone, G. T.** (1952). *Algebraic Projective Geometry*. Oxford University Press (Clarendon Press).
   - **Chapter IV (Projective Coordinates and Collineations in a Plane)**, Theorem 1 ("Fundamental Theorem of Projective Geometry for Collineations"), pp. 68–73:
     *Statement*: Three vertices of the triangle of reference $(1,0,0), (0,1,0), (0,0,1)$ together with the unit point $(1,1,1)$ constitute a canonical frame of reference; any collineation fixing the vertices of the reference triangle is represented by a diagonal matrix $\mathrm{diag}(\lambda_0, \lambda_1, \lambda_2)$, and also fixing the unit point forces $\lambda_0 = \lambda_1 = \lambda_2$.
     *Formalization*: `eq_diagonal_of_fixes_basis`, `homography_Arena_diagonal`, `scalars_eq_of_fixes_canonical_frame`, and `eq_smul_one_of_fixes_canonical_frame`.

3. **Faugeras, O., & Luong, Q.-T.** (2001). *The Geometry of Multiple Images*. MIT Press.
   - **Section 2.3 (Projective Bases and Homographies of $\mathbb{P}^2$)**, Proposition 2.3, pp. 26–29:
     Explicit construction of the change-of-basis matrix $B = [c_0 p_0, c_1 p_1, c_2 p_2]$ mapping the standard projective basis $(e_0, e_1, e_2, e_3)$ to an arbitrary 4-point projective basis $(p_0, p_1, p_2, p_3)$.
     *Formalization*: `frameBasisMatrix`, `frameBasisMatrix_mulVec_e₃`, `det_frameBasisMatrix`, and `homography_rigidity_of_general_position`.

---

## 5. Verification and Machine-Checked Proof Audit

- **Verification Command**:
  ```bash
  export PATH="$HOME/.elan/bin:$PATH" && lake env lean ControlsLean/Vision/HomographyUniqueness.lean
  ```
- **Exit Status**: `0`
- **Axiom Audit**: `#print axioms` on `eq_diagonal_of_fixes_basis`, `homography_Arena_diagonal`, `eq_smul_one_of_fixes_canonical_frame`, `homography_unique_on_canonical_frame`, `homography_unique_four_points`, `two_homographies_eq_smul_of_four_points`, and `homography_rigidity_of_general_position` confirms dependence solely on standard axioms `[propext, Classical.choice, Quot.sound]`.
- **Zero Escape Hatches**: Zero `sorry`, zero `admit`, zero custom `axiom` declarations.
