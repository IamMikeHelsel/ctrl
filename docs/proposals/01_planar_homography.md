# Planar Homographies, Projective Collineations, and Two-View Plane-Induced Motion in Lean 4

**Author**: Mike Helsel  
**Date**: October 17, 2026  
**Status**: Machine-Checked & Verified (`ControlsLean.Vision.Homography`)  
**Target Repository**: `ctrl` (`ControlsLean/Vision/Homography.lean`)  
**Axiom Footprint**: Standard Lean 4 axioms only (`[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero custom axioms)

---

## 1. Abstract

We formalize planar homographies, projective collineations, contragredient line transformations, determinant scaling, collinearity preservation, and plane-induced two-view motion constraints in Lean 4. In geometric computer vision, two-view epipolar geometry governed by the essential/fundamental matrix $x_2^\top E x_1 = 0$ is well known to degenerate when the observed 3D points lie on a plane $\pi$: all epipolar lines pass through the epipoles, rendering the 3D-to-2D correspondence unconstrained by the essential matrix. In this planar regime, image points are related by an invertible projective collineation $H \in \mathrm{GL}(3, K)$ such that $x_2 \propto H x_1$. 

We establish machine-checked proofs that:
1. Lines transform contragrediently ($l' = H^{-\top} l$), preserving point-line incidence: $(H^{-\top} l) \cdot (H p) = l \cdot p$.
2. The determinant of three transformed points scales by $\det(H)$: $\det [H p, H q, H r] = \det(H) \det [p, q, r]$.
3. Collinearity is strictly preserved under any non-singular collineation: $\det [H p, H q, H r] = 0 \iff \det [p, q, r] = 0$.
4. For calibrated cameras observing a 3D plane $n^\top X = d$ ($d \neq 0$) under rigid motion $(R, t)$, the plane-induced homography $H = R + \frac{1}{d} t n^\top$ exactly satisfies $H X = R X + t$, inducing the projective constraint $d_2 x_2 = H (d_1 x_1)$.

All results are formalized over an arbitrary characteristic-free field $K$ in `ControlsLean.Vision.Homography` with zero `sorry` and verified via `scripts/check.sh`.

---

## 2. Mathematical Formulation

### 2.1 Projective Plane and Collineations
Let $K$ be a field. The projective plane $\mathbb{P}^2(K)$ is the quotient space $(K^3 \setminus \{0\}) / \sim$, where points are represented by homogeneous coordinate rays $p \in K^3 \setminus \{0\}$ up to non-zero scalar equivalence. A line in $\mathbb{P}^2(K)$ is specified by a dual vector $l \in K^3 \setminus \{0\}$. A point $p$ lies on line $l$ if and only if:
$$l \cdot p = l^\top p = \sum_{i=0}^2 l_i p_i = 0.$$

A projective transformation (homography or collineation) is an invertible linear mapping $\mathbb{P}^2(K) \to \mathbb{P}^2(K)$ represented by an invertible matrix $H \in \mathrm{GL}(3, K)$. Under $H$, a point $p$ maps to:
$$p' = H p.$$

### 2.2 Dual Transformation of Lines (Contragredient Action)
To preserve the geometric incidence relation $l \cdot p = 0$ for all transformed points $p' = H p$ and transformed lines $l'$, the line must transform under the contragredient action:
$$l' = H^{-\top} l.$$
Taking the inner product:
$$l' \cdot p' = (H^{-\top} l)^\top (H p) = l^\top (H^{-1} H) p = l^\top p = l \cdot p.$$
Thus $p$ lies on $l$ if and only if $p'$ lies on $l'$.

### 2.3 Determinant Scaling and Collinearity Preservation
Three points $p, q, r \in K^3$ define the $3 \times 3$ column matrix $[p, q, r]$. Their transformed counterparts are $[H p, H q, H r] = H [p, q, r]$. By the multiplicativity of the determinant:
$$\det [H p, H q, H r] = \det(H [p, q, r]) = \det(H) \det [p, q, r].$$
Since $H$ is invertible ($\det(H) \neq 0$), it immediately follows that:
$$\det [H p, H q, H r] = 0 \iff \det [p, q, r] = 0.$$
This proves that three points are collinear in the projective plane if and only if their transformed images are collinear.

### 2.4 Homography Induced by a 3D Plane
Consider two calibrated pinhole cameras with relative rigid transformation $(R, t)$, where $R \in K^{3 \times 3}$ and $t \in K^3$. A point $X \in K^3$ in the reference frame of camera 1 transforms to camera 2 according to:
$$X_2 = R X_1 + t.$$

Suppose the scene points lie on a plane $\pi \subset K^3$ with unit normal $n \in K^3$ and perpendicular distance $d \in K \setminus \{0\}$ from the origin of camera 1:
$$n^\top X_1 = n \cdot X_1 = d.$$
Dividing by $d$:
$$\frac{n^\top X_1}{d} = 1.$$
Substituting this into the rigid motion equation:
$$X_2 = R X_1 + t (1) = R X_1 + t \left( \frac{n^\top X_1}{d} \right) = \left( R + \frac{1}{d} t n^\top \right) X_1.$$
Defining the plane-induced homography matrix:
$$H_\pi = R + \frac{1}{d} t n^\top \in K^{3 \times 3},$$
we have the exact linear relationship on 3D coordinates:
$$H_\pi X_1 = R X_1 + t = X_2.$$

In homogeneous perspective image coordinates, if $x_1, x_2 \in K^3$ represent the normalized ray coordinates with corresponding depths $d_1, d_2 \in K$ such that $X_1 = d_1 x_1$ and $X_2 = d_2 x_2 = R X_1 + t$, we obtain the exact projectivity:
$$d_2 x_2 = H_\pi (d_1 x_1).$$
Projectively (up to positive scale), $x_2 \propto H_\pi x_1$.

---

## 3. Formalization Architecture in Lean 4

The Lean 4 implementation is located in `ControlsLean/Vision/Homography.lean` and builds on Mathlib's `Matrix` and `ControlsLean.Vision.Epipolar`.

### 3.1 Design Decisions
1. **Characteristic-Free Base Field**:
   The entire theory is parameterized over a general field `[Field K]` without requiring $\mathbb{R}$. This ensures applicability to finite projective geometries $\mathbb{P}^2(\mathbb{F}_q)$ as well as standard real Euclidean vision spaces.
2. **Coordinate Vector Representation**:
   Points and lines are represented uniformly as vectors `Fin 3 → K`, and matrices as `Matrix (Fin 3) (Fin 3) K`. This directly interoperates with Mathlib's matrix-vector operations `*ᵥ`, vector dot products `⬝ᵥ`, and transpose `ᵀ`.
3. **Outer Product Infrastructure**:
   We define `outerProduct u v` as the rank-1 matrix $u v^\top$ and prove its action lemma `outerProduct_mulVec`:
   $$(u v^\top) x = (v \cdot x) u.$$
4. **Collinearity via Determinants**:
   Connecting with `ControlsLean.Vision.Epipolar.collinear_iff_det`, collinearity of three points is captured by the vanishing of the determinant $\det [p, q, r] = 0$.

### 3.2 Formal Lean 4 Definitions & Theorems

Below is the verified correspondence between the mathematical definitions and Lean 4 declarations:

#### Definitions
```lean
/-- Projective homography action on image points: `homography H x = H *ᵥ x`. -/
def homography (H : Matrix (Fin 3) (Fin 3) K) (x : Fin 3 → K) : Fin 3 → K :=
  H *ᵥ x

/-- Outer product `u vᵀ` as a 3x3 matrix: `(outerProduct u v) i j = u i * v j`. -/
def outerProduct (u v : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => u i * v j

/-- Line transformation under a projective homography `H` with inverse `H_inv`:
a line `l` transforms contragrediently by `l' = (H_inv)ᵀ *ᵥ l`. -/
def lineTransform (H_inv : Matrix (Fin 3) (Fin 3) K) (l : Fin 3 → K) : Fin 3 → K :=
  H_invᵀ *ᵥ l

/-- Homography matrix induced by a plane with normal `n` and distance `d`:
`H = R + (1 / d) • (t ⊗ n)`. -/
def homographyPlane (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d : K) :
    Matrix (Fin 3) (Fin 3) K :=
  R + d⁻¹ • outerProduct t n

/-- Alternative parameterized definition taking the inverse distance `d_inv = 1 / d`. -/
def planeHomography (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d_inv : K) :
    Matrix (Fin 3) (Fin 3) K :=
  R + d_inv • outerProduct t n
```

#### Headline Theorems
```lean
/-- Point-line incidence preservation under homography duality (Hartley & Zisserman Theorem 2.1). -/
theorem lineTransform_dotProduct (H H_inv : Matrix (Fin 3) (Fin 3) K)
    (hinv : H_inv * H = 1) (l p : Fin 3 → K) :
    (lineTransform H_inv l) ⬝ᵥ (H *ᵥ p) = l ⬝ᵥ p

/-- Incidence preservation iff. -/
theorem mem_lineTransform_iff (H H_inv : Matrix (Fin 3) (Fin 3) K)
    (hinv : H_inv * H = 1) (l p : Fin 3 → K) :
    (lineTransform H_inv l) ⬝ᵥ (H *ᵥ p) = 0 ↔ l ⬝ᵥ p = 0

/-- Determinant scaling of 3 transformed points. -/
theorem det_homography_three_points (H : Matrix (Fin 3) (Fin 3) K) (p q r : Fin 3 → K) :
    (Matrix.of ![H *ᵥ p, H *ᵥ q, H *ᵥ r]).det = H.det * (Matrix.of ![p, q, r]).det

/-- Collinearity preservation under projective collineation (Hartley & Zisserman Result 2.3). -/
theorem collinear_homography (H : Matrix (Fin 3) (Fin 3) K) (hH : H.det ≠ 0)
    (p q r : Fin 3 → K) :
    (Matrix.of ![H *ᵥ p, H *ᵥ q, H *ᵥ r]).det = 0 ↔ (Matrix.of ![p, q, r]).det = 0

/-- Plane-induced 3D motion constraint: H X = R X + t. -/
theorem plane_homography_mulVec (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d : K)
    (X : Fin 3 → K) (h_plane : n ⬝ᵥ X = d) (hd : d ≠ 0) :
    homographyPlane R t n d *ᵥ X = R *ᵥ X + t

/-- Two-view planar image correspondence (Hartley & Zisserman Theorem 13.1). -/
theorem plane_homography_constraint (R : Matrix (Fin 3) (Fin 3) K) (t n : Fin 3 → K) (d : K)
    (x₁ x₂ : Fin 3 → K) (d₁ d₂ : K) (hd : d ≠ 0)
    (h_plane : n ⬝ᵥ (d₁ • x₁) = d)
    (h_rigid : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) :
    d₂ • x₂ = homographyPlane R t n d *ᵥ (d₁ • x₁)
```

---

## 4. Novelty Analysis & Gap Positioning

To substantiate the novelty of this contribution, we conduct an explicit comparative audit against three baselines:

### 4.1 Comparison against Seed Codebase (`ControlsLean.Vision.Epipolar`)
- **Seed Baseline**: `ControlsLean.Vision.Epipolar` formalizes the 3D calibrated two-view epipolar constraint $x_2^\top E x_1 = 0$ with $E = [t]_\times R$, the singularity of the essential matrix $\det(E) = 0$, and the left-nullspace property $t^\top E = 0$.
- **Fundamental Geometric Limitation**: Epipolar geometry is valid only for general (non-coplanar) 3D point configurations. When all scene points lie on a single plane $\pi$, the fundamental/essential matrix cannot be uniquely estimated (it suffers from a 2-parameter ambiguity), and the epipolar constraint becomes degenerate because epipolar lines collapse or become identical for all points on lines passing through the epipole.
- **Novelty of Homography**: `ControlsLean.Vision.Homography` solves this planar degeneracy by providing the exact $3 \times 3$ projective collineation $H = R + \frac{1}{d} t n^\top$. Furthermore, it introduces projective duality (contragredient transformation of lines $l' = H^{-\top} l$) and projective geometric invariants (determinant scaling and collinearity preservation), none of which exist in `Epipolar.lean`.

### 4.2 Comparison against Mathlib
- **Mathlib Baseline**: Mathlib provides general matrix algebra (`Matrix.mul`, `Matrix.det`, `Matrix.transpose`) and 3D cross products (`Mathlib.LinearAlgebra.CrossProduct`).
- **Absence**: Mathlib contains zero definitions or theorems pertaining to projective computer vision: no pinhole camera models, no homographies, no projective collineations, no planar motion constraints, and no duality theorems for lines and points under projective transformations.

### 4.3 Comparison against `LeanForControl`
- **Reference Baseline**: The 66 modules of `/Users/mike/Dev/LeanForControl` focus strictly on state-space control theory (controllability, observability, Hautus PBH tests, Kalman canonical decomposition, and Lyapunov equations).
- **Absence**: `LeanForControl` contains 0 modules in computer vision or image geometry.

---

## 5. Literature Grounding & Citations

1. **Hartley, R., & Zisserman, A.** (2004). *Multiple View Geometry in Computer Vision* (2nd ed.). Cambridge University Press.
   - **Theorem 2.1 (Transformation of lines)**, p. 36:
     *Statement*: Under a point transformation $x' = H x$, a line transforms as $l' = H^{-\top} l$.
     *Formalization*: `lineTransform_dotProduct` and `mem_lineTransform_iff`.
   - **Result 2.3 (Collinearity invariance)**, p. 37:
     *Statement*: Projective transformations map collinear points to collinear points, and concurrent lines to concurrent lines.
     *Formalization*: `det_homography_three_points` and `collinear_homography`.
   - **Theorem 13.1 (Homography induced by a plane)**, p. 327, Eq. (13.1):
     *Statement*: Given two cameras with projection matrices $P = [I \mid 0]$ and $P' = [R \mid t]$, the homography induced by a world plane $\pi = (n^\top, -d)^\top$ satisfies $H = R + \frac{1}{d} t n^\top$.
     *Formalization*: `plane_homography_mulVec` and `plane_homography_constraint`.

2. **Faugeras, O., & Luong, Q.-T.** (2001). *The Geometry of Multiple Images: The Laws That Govern the Formation of Multiple Images of a Scene and Some of Their Applications*. MIT Press.
   - **Chapter 5 (Projective Properties of Planes)**, Sections 5.1–5.3, pp. 147–164:
     Exposition of planar homographies as isomorphisms between projective planes, planar motion estimation, and homography decomposition into rotation, translation, and plane normal.

3. **Ma, Y., Soatto, S., Kosecka, J., & Sastry, S. S.** (2004). *An Invitation to 3-D Vision: From Images to Geometric Models*. Springer-Verlag.
   - **Chapter 5 (Planar Scenes and Homographies)**, Section 5.3 ("Homography Induced by a Plane"), pp. 135–142:
     Detailed derivation of the planar homography matrix $H = R + \frac{1}{d} t n^\top$ and its role in visual servoing, image registration, and visual odometry over planar terrain.

4. **Zhang, Z.** (2000). "A flexible new technique for camera calibration." *IEEE Transactions on Pattern Analysis and Machine Intelligence*, 22(11): 1330–1334.
   - Foundational computer vision algorithm utilizing planar homographies of a planar checkerboard pattern to estimate intrinsic and extrinsic camera parameters.

---

## 6. Verification and Machine-Checked Proof Audit

The formalization was machine-checked using Lean 4.36.0-rc1 with Lake:
- **Command**:
  ```bash
  export PATH="$HOME/.elan/bin:$PATH"; bash scripts/check.sh ControlsLean/Vision/Homography.lean
  ```
- **Exit Status**: `0`
- **Axioms**: All declarations depend strictly on the standard foundational axioms:
  - `propext` (Propositional extensionality)
  - `Classical.choice` (Axiom of choice)
  - `Quot.sound` (Quotient soundness)
- **Zero Escape Hatches**: No `sorry`, `admit`, or custom `axiom` declarations exist in the code.
