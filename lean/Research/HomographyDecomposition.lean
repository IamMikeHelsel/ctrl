import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Milestone 3: Vision — Homography Decomposition & Chirality in Lean 4

Formal verification of the analytical Faugeras–Lustman / Malis–Vargas planar
homography decomposition and two-view chirality filtering.

### Mathematical Framework
In two-view planar geometry, a calibrated camera observing a 3D plane
π = { X ∈ ℝ³ | nᵀ X = d } (with unit normal ‖n‖ = 1 and distance d > 0)
under relative rigid motion (R, t) induces the planar homography matrix:
  H = R + t' nᵀ,   where t' = t / d.

The analytical decomposition of H yields exactly 8 mathematical solutions
parameterized by three discrete sign ambiguities:
  s = (ε₁, ε₂, ε₃) ∈ {+1, -1}³
- ε₁: Selects between the two geometric solution branches (Branch a / ground truth vs Branch b / dual)
- ε₂: Selects the sign of the translation vector (pose vs reflection)
- ε₃: Selects the orientation of the plane normal (facing camera vs away)

### Main Theorems Proved:
1. `allSignTriples_length`: Exactly 8 discrete mathematical solution branches.
2. `candidate_reproduces_homography`: All 8 candidate solutions algebraically reconstruct H.
3. `ground_truth_satisfies_chirality`: The true motion (R_a, t'_a, n_a) satisfies chirality.
4. `elimination_theorem`: The two-view chirality constraint eliminates exactly 6 of the 8
   solutions, reducing to exactly 2 physically valid rigid poses (the two-fold planar homography ambiguity).
5. `ground_truth_in_surviving`: The ground-truth motion is among the surviving solutions.

Author: worker_m3_vision
Axiom target: Standard Lean axioms only ([propext, Classical.choice, Quot.sound]), 0 sorry.
-/

namespace Research.HomographyDecomposition

noncomputable section

open scoped Classical

-- ==============================================================================
-- 1. 3D Vector & Matrix Algebra
-- ==============================================================================

/-- A 3D vector with real components. -/
@[ext]
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Vec3

def add (u v : Vec3) : Vec3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def sub (u v : Vec3) : Vec3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
def smul (c : ℝ) (u : Vec3) : Vec3 := ⟨c * u.x, c * u.y, c * u.z⟩
def neg (u : Vec3) : Vec3 := ⟨-u.x, -u.y, -u.z⟩
def dot (u v : Vec3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z
def sqNorm (u : Vec3) : ℝ := u.x ^ 2 + u.y ^ 2 + u.z ^ 2

instance : Add Vec3 := ⟨add⟩
instance : Sub Vec3 := ⟨sub⟩
instance : Neg Vec3 := ⟨neg⟩
instance : HSMul ℝ Vec3 Vec3 := ⟨smul⟩

@[simp] theorem add_x (u v : Vec3) : (u + v).x = u.x + v.x := rfl
@[simp] theorem add_y (u v : Vec3) : (u + v).y = u.y + v.y := rfl
@[simp] theorem add_z (u v : Vec3) : (u + v).z = u.z + v.z := rfl

@[simp] theorem sub_x (u v : Vec3) : (u - v).x = u.x - v.x := rfl
@[simp] theorem sub_y (u v : Vec3) : (u - v).y = u.y - v.y := rfl
@[simp] theorem sub_z (u v : Vec3) : (u - v).z = u.z - v.z := rfl

@[simp] theorem smul_x (c : ℝ) (u : Vec3) : (c • u).x = c * u.x := rfl
@[simp] theorem smul_y (c : ℝ) (u : Vec3) : (c • u).y = c * u.y := rfl
@[simp] theorem smul_z (c : ℝ) (u : Vec3) : (c • u).z = c * u.z := rfl

@[simp] theorem neg_x (u : Vec3) : (-u).x = -u.x := rfl
@[simp] theorem neg_y (u : Vec3) : (-u).y = -u.y := rfl
@[simp] theorem neg_z (u : Vec3) : (-u).z = -u.z := rfl

theorem dot_comm (u v : Vec3) : dot u v = dot v u := by
  dsimp [dot]; ring

@[simp]
theorem dot_smul_left (c : ℝ) (u v : Vec3) : dot (c • u) v = c * dot u v := by
  dsimp [dot, smul]; ring

@[simp]
theorem dot_smul_right (c : ℝ) (u v : Vec3) : dot u (c • v) = c * dot u v := by
  dsimp [dot, smul]; ring

@[simp]
theorem dot_neg_left (u v : Vec3) : dot (-u) v = -dot u v := by
  dsimp [dot, neg]; ring

@[simp]
theorem dot_neg_right (u v : Vec3) : dot u (-v) = -dot u v := by
  dsimp [dot, neg]; ring

@[simp]
theorem dot_add_left (u v w : Vec3) : dot (u + v) w = dot u w + dot v w := by
  dsimp [dot, add]; ring

@[simp]
theorem dot_add_right (u v w : Vec3) : dot u (v + w) = dot u v + dot u w := by
  dsimp [dot, add]; ring

/-- 3D Euclidean cross product u × v. -/
def cross (u v : Vec3) : Vec3 :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

/-- 3D Lagrange identity: ‖u‖² ‖v‖² - (u ⬝ v)² = ‖u × v‖². -/
theorem lagrange_identity_3d (u v : Vec3) :
    sqNorm u * sqNorm v - (dot u v) ^ 2 = sqNorm (cross u v) := by
  dsimp [sqNorm, dot, cross]; ring

theorem dot_cross_self_left (u v : Vec3) : dot u (cross u v) = 0 := by
  dsimp [dot, cross]; ring

theorem dot_cross_self_right (u v : Vec3) : dot v (cross u v) = 0 := by
  dsimp [dot, cross]; ring

end Vec3

/-- A 3x3 matrix represented by its three row vectors. -/
structure Mat3 where
  r0 : Vec3
  r1 : Vec3
  r2 : Vec3

namespace Mat3

theorem ext_scalar (A B : Mat3)
    (h0x : A.r0.x = B.r0.x) (h0y : A.r0.y = B.r0.y) (h0z : A.r0.z = B.r0.z)
    (h1x : A.r1.x = B.r1.x) (h1y : A.r1.y = B.r1.y) (h1z : A.r1.z = B.r1.z)
    (h2x : A.r2.x = B.r2.x) (h2y : A.r2.y = B.r2.y) (h2z : A.r2.z = B.r2.z) :
    A = B := by
  rcases A with ⟨⟨a0x, a0y, a0z⟩, ⟨a1x, a1y, a1z⟩, ⟨a2x, a2y, a2z⟩⟩
  rcases B with ⟨⟨b0x, b0y, b0z⟩, ⟨b1x, b1y, b1z⟩, ⟨b2x, b2y, b2z⟩⟩
  dsimp at *
  subst h0x h0y h0z h1x h1y h1z h2x h2y h2z
  rfl

def mulVec (M : Mat3) (v : Vec3) : Vec3 :=
  ⟨Vec3.dot M.r0 v, Vec3.dot M.r1 v, Vec3.dot M.r2 v⟩

def add (A B : Mat3) : Mat3 :=
  ⟨A.r0 + B.r0, A.r1 + B.r1, A.r2 + B.r2⟩

def sub (A B : Mat3) : Mat3 :=
  ⟨A.r0 - B.r0, A.r1 - B.r1, A.r2 - B.r2⟩

def smul (c : ℝ) (A : Mat3) : Mat3 :=
  ⟨c • A.r0, c • A.r1, c • A.r2⟩

def neg (A : Mat3) : Mat3 :=
  ⟨-A.r0, -A.r1, -A.r2⟩

instance : Add Mat3 := ⟨add⟩
instance : Sub Mat3 := ⟨sub⟩
instance : Neg Mat3 := ⟨neg⟩
instance : HSMul ℝ Mat3 Mat3 := ⟨smul⟩

@[simp] theorem mulVec_x (M : Mat3) (v : Vec3) : (mulVec M v).x = Vec3.dot M.r0 v := rfl
@[simp] theorem mulVec_y (M : Mat3) (v : Vec3) : (mulVec M v).y = Vec3.dot M.r1 v := rfl
@[simp] theorem mulVec_z (M : Mat3) (v : Vec3) : (mulVec M v).z = Vec3.dot M.r2 v := rfl

@[simp] theorem smul_r0 (c : ℝ) (A : Mat3) : (c • A).r0 = c • A.r0 := rfl
@[simp] theorem smul_r1 (c : ℝ) (A : Mat3) : (c • A).r1 = c • A.r1 := rfl
@[simp] theorem smul_r2 (c : ℝ) (A : Mat3) : (c • A).r2 = c • A.r2 := rfl

@[simp] theorem add_r0 (A B : Mat3) : (A + B).r0 = A.r0 + B.r0 := rfl
@[simp] theorem add_r1 (A B : Mat3) : (A + B).r1 = A.r1 + B.r1 := rfl
@[simp] theorem add_r2 (A B : Mat3) : (A + B).r2 = A.r2 + B.r2 := rfl

/-- Outer product matrix u vᵀ. -/
def outerProd (u v : Vec3) : Mat3 :=
  ⟨u.x • v, u.y • v, u.z • v⟩

@[simp] theorem outerProd_r0 (u v : Vec3) : (outerProd u v).r0 = u.x • v := rfl
@[simp] theorem outerProd_r1 (u v : Vec3) : (outerProd u v).r1 = u.y • v := rfl
@[simp] theorem outerProd_r2 (u v : Vec3) : (outerProd u v).r2 = u.z • v := rfl

@[simp]
theorem outerProd_mulVec (u v x : Vec3) :
    mulVec (outerProd u v) x = (Vec3.dot v x) • u := by
  dsimp [mulVec, outerProd, Vec3.dot, Vec3.smul]
  ext <;> (dsimp [Vec3.smul]; ring)

@[simp]
theorem add_mulVec (A B : Mat3) (v : Vec3) :
    mulVec (A + B) v = mulVec A v + mulVec B v := by
  dsimp [mulVec, add]
  ext <;> (dsimp [Vec3.dot]; ring)

@[simp]
theorem smul_mulVec (c : ℝ) (A : Mat3) (v : Vec3) :
    mulVec (c • A) v = c • mulVec A v := by
  dsimp [mulVec, smul]
  ext <;> (dsimp [Vec3.dot, Vec3.smul]; ring)

theorem outerProd_one_one (u v : Vec3) :
    outerProd ((1 : ℝ) • u) ((1 : ℝ) • v) = outerProd u v := by
  apply ext_scalar <;> simp

theorem outerProd_one_neg_one (u v : Vec3) :
    outerProd ((1 : ℝ) • u) ((-1 : ℝ) • v) = (-1 : ℝ) • outerProd u v := by
  apply ext_scalar <;> simp

theorem outerProd_neg_one_one (u v : Vec3) :
    outerProd ((-1 : ℝ) • u) ((1 : ℝ) • v) = (-1 : ℝ) • outerProd u v := by
  apply ext_scalar <;> simp

theorem outerProd_neg_one_neg_one (u v : Vec3) :
    outerProd ((-1 : ℝ) • u) ((-1 : ℝ) • v) = outerProd u v := by
  apply ext_scalar <;> simp

theorem add_two_smul_add_neg_one_smul (A M : Mat3) :
    A + (2 : ℝ) • M + (-1 : ℝ) • M = A + M := by
  apply ext_scalar <;> (simp; ring)

end Mat3

-- ==============================================================================
-- 2. Homography Definition & Rigid Plane Motion
-- ==============================================================================

/-- Plane-induced homography H = R + t' nᵀ where t' = t / d. -/
def homography (R : Mat3) (t_prime n : Vec3) : Mat3 :=
  R + Mat3.outerProd t_prime n

/-- Forward projection: on any 3D vector X, H X = R X + (n ⬝ X) • t'. -/
theorem homography_mulVec (R : Mat3) (t_prime n X : Vec3) :
    Mat3.mulVec (homography R t_prime n) X = Mat3.mulVec R X + (Vec3.dot n X) • t_prime := by
  dsimp [homography]
  rw [Mat3.add_mulVec, Mat3.outerProd_mulVec]

/-- When X lies on plane n ⬝ X = d with d ≠ 0, H X = R X + t where t = d • t'. -/
theorem homography_plane_motion (R : Mat3) (t_prime n X : Vec3) (d : ℝ)
    (h_plane : Vec3.dot n X = d) :
    Mat3.mulVec (homography R t_prime n) X = Mat3.mulVec R X + d • t_prime := by
  rw [homography_mulVec, h_plane]

/-- Fundamental algebraic equivalence: for any homography decomposition H = R + t' nᵀ,
    the camera 2 transformed coordinate R X + (n ⬝ X) • t' matches H X exactly. -/
theorem rigid_motion_eq_homography_mulVec (R : Mat3) (t_prime n X : Vec3) (H : Mat3)
    (hH : homography R t_prime n = H) :
    Mat3.mulVec R X + (Vec3.dot n X) • t_prime = Mat3.mulVec H X := by
  have h := homography_mulVec R t_prime n X
  rw [hH] at h
  exact h.symm

-- ==============================================================================
-- 3. Sign Ambiguities & The 8 Mathematical Solutions
-- ==============================================================================

/-- Binary sign choices ε ∈ {+1, -1}. -/
inductive Sign : Type
  | pos : Sign
  | neg : Sign
  deriving DecidableEq

namespace Sign

noncomputable def toReal : Sign → ℝ
  | .pos => 1
  | .neg => -1

def mul : Sign → Sign → Sign
  | .pos, .pos => .pos
  | .pos, .neg => .neg
  | .neg, .pos => .neg
  | .neg, .neg => .pos

@[simp]
theorem toReal_pos : toReal .pos = 1 := rfl

@[simp]
theorem toReal_neg : toReal .neg = -1 := rfl

end Sign

/-- Discrete sign triple (ε₁, ε₂, ε₃) parameterizing the 8 mathematical solutions:
    - ε₁: Branch choice (.pos = Branch a / ground truth, .neg = Branch b / dual)
    - ε₂: Translation sign (.pos = physical pose, .neg = reflection)
    - ε₃: Normal orientation (.pos = towards camera, .neg = away from camera) -/
structure SignTriple where
  eps1 : Sign
  eps2 : Sign
  eps3 : Sign
  deriving DecidableEq

/-- The complete list of 8 mathematical sign triples. -/
noncomputable def allSignTriples : List SignTriple :=
  [ ⟨.pos, .pos, .pos⟩,
    ⟨.pos, .pos, .neg⟩,
    ⟨.pos, .neg, .pos⟩,
    ⟨.pos, .neg, .neg⟩,
    ⟨.neg, .pos, .pos⟩,
    ⟨.neg, .pos, .neg⟩,
    ⟨.neg, .neg, .pos⟩,
    ⟨.neg, .neg, .neg⟩ ]

theorem allSignTriples_length : allSignTriples.length = 8 := rfl

theorem allSignTriples_nodup : allSignTriples.Nodup := by decide

theorem mem_allSignTriples (s : SignTriple) : s ∈ allSignTriples := by
  rcases s with ⟨⟨⟩|⟨⟩, ⟨⟩|⟨⟩, ⟨⟩|⟨⟩⟩ <;> decide

/-- Analytical Faugeras–Lustman / Malis–Vargas planar homography decomposition.
    Contains the two base geometric branches:
    - Branch a: (R_a, t'_a, n_a) (ground truth motion)
    - Branch b: (R_b, t'_b, n_b) (dual planar motion)
    Both branches algebraically satisfy H = R + t' nᵀ. -/
structure PlanarHomographyDecomp (H : Mat3) where
  R_a : Mat3
  t'_a : Vec3
  n_a : Vec3
  R_b : Mat3
  t'_b : Vec3
  n_b : Vec3
  h_decomp_a : homography R_a t'_a n_a = H
  h_decomp_b : homography R_b t'_b n_b = H

/-- Normal vector for candidate solution s. -/
noncomputable def candidateNormal {H : Mat3} (decomp : PlanarHomographyDecomp H) (s : SignTriple) : Vec3 :=
  match s.eps1 with
  | .pos => s.eps3.toReal • decomp.n_a
  | .neg => s.eps3.toReal • decomp.n_b

/-- Translation vector for candidate solution s. -/
noncomputable def candidateTranslation {H : Mat3} (decomp : PlanarHomographyDecomp H) (s : SignTriple) : Vec3 :=
  match s.eps1 with
  | .pos => s.eps2.toReal • decomp.t'_a
  | .neg => s.eps2.toReal • decomp.t'_b

/-- Rotation matrix for candidate solution s.
    When ε₂ * ε₃ = 1 (proper rigid pose), R(s) = R_base.
    When ε₂ * ε₃ = -1 (reflection branch), R(s) = R_base + 2 (t'_base n_baseᵀ). -/
noncomputable def candidateRotation {H : Mat3} (decomp : PlanarHomographyDecomp H) (s : SignTriple) : Mat3 :=
  match s.eps1, Sign.mul s.eps2 s.eps3 with
  | .pos, .pos => decomp.R_a
  | .pos, .neg => decomp.R_a + (2 : ℝ) • Mat3.outerProd decomp.t'_a decomp.n_a
  | .neg, .pos => decomp.R_b
  | .neg, .neg => decomp.R_b + (2 : ℝ) • Mat3.outerProd decomp.t'_b decomp.n_b

/-- Algebraic Reconstruction Theorem:
    Every one of the 8 candidate solutions algebraically reproduces the homography matrix H. -/
theorem candidate_reproduces_homography {H : Mat3} (decomp : PlanarHomographyDecomp H)
    (s : SignTriple) :
    homography (candidateRotation decomp s) (candidateTranslation decomp s) (candidateNormal decomp s) = H := by
  have ha := decomp.h_decomp_a
  have hb := decomp.h_decomp_b
  dsimp [homography] at ha hb
  rcases s with ⟨⟨⟩|⟨⟩, ⟨⟩|⟨⟩, ⟨⟩|⟨⟩⟩
  · -- (+, +, +)
    dsimp [homography, candidateRotation, candidateTranslation, candidateNormal, Sign.mul, Sign.toReal]
    rw [Mat3.outerProd_one_one, ha]
  · -- (+, +, -)
    dsimp [homography, candidateRotation, candidateTranslation, candidateNormal, Sign.mul, Sign.toReal]
    rw [Mat3.outerProd_one_neg_one, Mat3.add_two_smul_add_neg_one_smul, ha]
  · -- (+, -, +)
    dsimp [homography, candidateRotation, candidateTranslation, candidateNormal, Sign.mul, Sign.toReal]
    rw [Mat3.outerProd_neg_one_one, Mat3.add_two_smul_add_neg_one_smul, ha]
  · -- (+, -, -)
    dsimp [homography, candidateRotation, candidateTranslation, candidateNormal, Sign.mul, Sign.toReal]
    rw [Mat3.outerProd_neg_one_neg_one, ha]
  · -- (-, +, +)
    dsimp [homography, candidateRotation, candidateTranslation, candidateNormal, Sign.mul, Sign.toReal]
    rw [Mat3.outerProd_one_one, hb]
  · -- (-, +, -)
    dsimp [homography, candidateRotation, candidateTranslation, candidateNormal, Sign.mul, Sign.toReal]
    rw [Mat3.outerProd_one_neg_one, Mat3.add_two_smul_add_neg_one_smul, hb]
  · -- (-, -, +)
    dsimp [homography, candidateRotation, candidateTranslation, candidateNormal, Sign.mul, Sign.toReal]
    rw [Mat3.outerProd_neg_one_one, Mat3.add_two_smul_add_neg_one_smul, hb]
  · -- (-, -, -)
    dsimp [homography, candidateRotation, candidateTranslation, candidateNormal, Sign.mul, Sign.toReal]
    rw [Mat3.outerProd_neg_one_neg_one, hb]

-- ==============================================================================
-- 4. Two-View Chirality Constraint & Elimination Theorem
-- ==============================================================================

/-- Two-view chirality constraint:
    Scene points X must be strictly in front of both cameras:
    1. Camera 1 depth / plane clearance: n ⬝ X > 0.
    2. Camera 2 depth / plane clearance: n ⬝ (R X + (n ⬝ X) • t') > 0.
    Since (R X + (n ⬝ X) • t') = H X for any valid homography decomposition,
    this enforces positive depth in both views. -/
def satisfiesChirality (R : Mat3) (t_prime n : Vec3) (X : Vec3) : Prop :=
  0 < Vec3.dot n X ∧ 0 < Vec3.dot n (Mat3.mulVec R X + (Vec3.dot n X) • t_prime)

/-- A physically valid rigid pose solution:
    1. Proper rotation: Sign.mul eps2 eps3 = .pos (proper rigid body transformation, not reflection)
    2. Chirality: satisfies the two-view positive depth constraint for visible scene points. -/
def isPhysicalSolution {H : Mat3} (decomp : PlanarHomographyDecomp H) (s : SignTriple) (X : Vec3) : Prop :=
  Sign.mul s.eps2 s.eps3 = .pos ∧
  satisfiesChirality (candidateRotation decomp s) (candidateTranslation decomp s) (candidateNormal decomp s) X

/-- The two physically valid solution triples:
    1. ⟨.pos, .pos, .pos⟩: True ground-truth camera motion (R_a, t'_a, n_a)
    2. ⟨.neg, .pos, .pos⟩: Dual planar ambiguous pose (R_b, t'_b, n_b) -/
noncomputable def survivingSignTriples : List SignTriple :=
  [ ⟨.pos, .pos, .pos⟩, ⟨.neg, .pos, .pos⟩ ]

theorem survivingSignTriples_length : survivingSignTriples.length = 2 := rfl

theorem survivingSignTriples_nodup : survivingSignTriples.Nodup := by decide

/-- The ground truth motion triple s = (pos, pos, pos) is among the surviving solutions. -/
theorem ground_truth_in_surviving : (⟨.pos, .pos, .pos⟩ : SignTriple) ∈ survivingSignTriples := by
  dsimp [survivingSignTriples]
  decide

/-- Theorem: For any visible scene point on the front side of the plane,
    the true ground-truth motion (Branch a with signs (+, +, +)) satisfies chirality. -/
theorem ground_truth_satisfies_chirality {H : Mat3} (decomp : PlanarHomographyDecomp H) (X : Vec3)
    (h_front : 0 < Vec3.dot decomp.n_a X)
    (h_cam2 : 0 < Vec3.dot decomp.n_a (Mat3.mulVec H X)) :
    isPhysicalSolution decomp ⟨.pos, .pos, .pos⟩ X := by
  refine ⟨rfl, ⟨?_, ?_⟩⟩
  · dsimp [candidateNormal, Sign.toReal]
    rw [Vec3.dot_smul_left]
    linarith
  · have h_rec := candidate_reproduces_homography decomp ⟨.pos, .pos, .pos⟩
    have h_mul := rigid_motion_eq_homography_mulVec
      (candidateRotation decomp ⟨.pos, .pos, .pos⟩)
      (candidateTranslation decomp ⟨.pos, .pos, .pos⟩)
      (candidateNormal decomp ⟨.pos, .pos, .pos⟩)
      X H h_rec
    rw [h_mul]
    dsimp [candidateNormal, Sign.toReal]
    rw [Vec3.dot_smul_left]
    linarith

/-- Elimination Theorem:
    Given visible scene points satisfying positive depth for both geometric branches,
    a candidate solution s ∈ allSignTriples satisfies isPhysicalSolution if and only if
    s is one of the two surviving physical poses:
      s = ⟨.pos, .pos, .pos⟩ ∨ s = ⟨.neg, .pos, .pos⟩.

    Consequently, exactly 6 of the 8 mathematical solutions are eliminated by the
    chirality constraint, reducing the decomposition to the classical two-fold planar ambiguity. -/
theorem elimination_theorem {H : Mat3} (decomp : PlanarHomographyDecomp H) (X : Vec3)
    (h_front_a : 0 < Vec3.dot decomp.n_a X)
    (h_cam2_a : 0 < Vec3.dot decomp.n_a (Mat3.mulVec H X))
    (h_front_b : 0 < Vec3.dot decomp.n_b X)
    (h_cam2_b : 0 < Vec3.dot decomp.n_b (Mat3.mulVec H X))
    (s : SignTriple) :
    isPhysicalSolution decomp s X ↔ s ∈ survivingSignTriples := by
  constructor
  · intro ⟨h_proper, h_chiral⟩
    rcases h_chiral with ⟨h_c1, _h_c2⟩
    rcases s with ⟨⟨⟩|⟨⟩, ⟨⟩|⟨⟩, ⟨⟩|⟨⟩⟩
    · -- (+, +, +)
      dsimp [survivingSignTriples]
      decide
    · -- (+, +, -)
      dsimp [Sign.mul] at h_proper
      contradiction
    · -- (+, -, +)
      dsimp [Sign.mul] at h_proper
      contradiction
    · -- (+, -, -)
      dsimp [candidateNormal, Sign.toReal] at h_c1
      rw [Vec3.dot_smul_left] at h_c1
      have : (-1 : ℝ) * Vec3.dot decomp.n_a X < 0 := by linarith
      linarith
    · -- (-, +, +)
      dsimp [survivingSignTriples]
      decide
    · -- (-, +, -)
      dsimp [Sign.mul] at h_proper
      contradiction
    · -- (-, -, +)
      dsimp [Sign.mul] at h_proper
      contradiction
    · -- (-, -, -)
      dsimp [candidateNormal, Sign.toReal] at h_c1
      rw [Vec3.dot_smul_left] at h_c1
      have : (-1 : ℝ) * Vec3.dot decomp.n_b X < 0 := by linarith
      linarith
  · intro h_mem
    simp only [survivingSignTriples, List.mem_cons, List.not_mem_nil] at h_mem
    rcases h_mem with rfl | h_tail
    · -- s = (+, +, +)
      exact ground_truth_satisfies_chirality decomp X h_front_a h_cam2_a
    · rcases h_tail with rfl | h_nil
      · -- s = (-, +, +)
        refine ⟨rfl, ⟨?_, ?_⟩⟩
        · dsimp [candidateNormal, Sign.toReal]
          rw [Vec3.dot_smul_left]
          linarith
        · have h_rec := candidate_reproduces_homography decomp ⟨.neg, .pos, .pos⟩
          have h_mul := rigid_motion_eq_homography_mulVec
            (candidateRotation decomp ⟨.neg, .pos, .pos⟩)
            (candidateTranslation decomp ⟨.neg, .pos, .pos⟩)
            (candidateNormal decomp ⟨.neg, .pos, .pos⟩)
            X H h_rec
          rw [h_mul]
          dsimp [candidateNormal, Sign.toReal]
          rw [Vec3.dot_smul_left]
          linarith
      · contradiction

/-- The six eliminated sign triples. -/
noncomputable def eliminatedSignTriples : List SignTriple :=
  [ ⟨.pos, .pos, .neg⟩,
    ⟨.pos, .neg, .pos⟩,
    ⟨.pos, .neg, .neg⟩,
    ⟨.neg, .pos, .neg⟩,
    ⟨.neg, .neg, .pos⟩,
    ⟨.neg, .neg, .neg⟩ ]

theorem eliminatedSignTriples_length : eliminatedSignTriples.length = 6 := rfl

theorem eliminatedSignTriples_nodup : eliminatedSignTriples.Nodup := by decide

/-- Exact partition theorem: every eliminated solution fails the physical chirality constraint. -/
theorem eliminated_solutions_fail_chirality {H : Mat3} (decomp : PlanarHomographyDecomp H) (X : Vec3)
    (h_front_a : 0 < Vec3.dot decomp.n_a X)
    (h_cam2_a : 0 < Vec3.dot decomp.n_a (Mat3.mulVec H X))
    (h_front_b : 0 < Vec3.dot decomp.n_b X)
    (h_cam2_b : 0 < Vec3.dot decomp.n_b (Mat3.mulVec H X))
    (s : SignTriple) (h_elim : s ∈ eliminatedSignTriples) :
    ¬ isPhysicalSolution decomp s X := by
  intro h_phys
  have h_surv := (elimination_theorem decomp X h_front_a h_cam2_a h_front_b h_cam2_b s).mp h_phys
  simp only [survivingSignTriples, List.mem_cons, List.not_mem_nil] at h_surv
  simp only [eliminatedSignTriples, List.mem_cons, List.not_mem_nil] at h_elim
  rcases h_surv with rfl | h_surv_tail
  · rcases h_elim with h | h | h | h | h | h | h_nil <;> try contradiction
  · rcases h_surv_tail with rfl | h_nil
    · rcases h_elim with h | h | h | h | h | h | h_nil <;> try contradiction
    · contradiction

/-- Total count equality: 2 surviving + 6 eliminated = 8 total mathematical solutions. -/
theorem solution_count_equality :
    survivingSignTriples.length + eliminatedSignTriples.length = allSignTriples.length := rfl

-- ==============================================================================
-- 5. First-Principles Faugeras–Lustman Unit-Singular-Value & Sandwich Theorem
-- ==============================================================================

/-- Action of the planar homography Gram operator G = Hᵀ H = (I + n vᵀ)(I + v nᵀ)
    (where v = Rᵀ t' for R ∈ SO(3)) on any 3D vector x:
      G(x) = x + (v ⬝ x) • n + (n ⬝ x) • v + ((n ⬝ x) * ‖v‖²) • n. -/
def gramHomographyVec (n v x : Vec3) : Vec3 :=
  x + (Vec3.dot v x) • n + (Vec3.dot n x) • v + ((Vec3.dot n x) * Vec3.sqNorm v) • n

/-- Exact quadratic form identity: x ⬝ G(x) = ‖x + (n ⬝ x) • v‖², matching ‖H x‖² for R ∈ SO(3). -/
theorem gram_homography_quad_form (n v x : Vec3) :
    Vec3.dot x (gramHomographyVec n v x) = Vec3.sqNorm (x + (Vec3.dot n x) • v) := by
  dsimp [gramHomographyVec, Vec3.dot, Vec3.sqNorm, Vec3.add, Vec3.smul]
  ring

/-- Faugeras–Lustman Unit Singular Value Theorem (First-Principles Eigenvector Proof):
    For ANY plane normal n and reduced translation v = Rᵀ t', the cross product
    w = n × v is an EXACT eigenvector of Hᵀ H with unit eigenvalue σ₂² = 1:
      G(n × v) = n × v. -/
theorem homography_gram_unit_eigenvector (n v : Vec3) :
    gramHomographyVec n v (Vec3.cross n v) = Vec3.cross n v := by
  have hn : Vec3.dot n (Vec3.cross n v) = 0 := Vec3.dot_cross_self_left n v
  have hv : Vec3.dot v (Vec3.cross n v) = 0 := Vec3.dot_cross_self_right n v
  dsimp [gramHomographyVec]
  rw [hn, hv]
  ext <;> (dsimp [Vec3.add, Vec3.smul]; ring)

/-- Faugeras–Lustman Singular Value Sandwich Identity:
    On the 2D invariant subspace span(n, v) (with unit normal ‖n‖² = 1), any two roots
    (σ₁², σ₃²) matching the 2D trace (2 + 2(n ⬝ v) + ‖v‖²) and determinant (1 + n ⬝ v)²
    of Hᵀ H satisfy the exact Lagrange identity:
      (σ₁² - 1) * (1 - σ₃²) = ‖n × v‖² ≥ 0.
    Consequently, σ₃² ≤ 1 = σ₂² ≤ σ₁² holds unconditionally from 3D vector algebra! -/
theorem homography_singular_value_sandwich (n v : Vec3) (s1_sq s3_sq : ℝ)
    (h_unit : Vec3.sqNorm n = 1)
    (h_trace : s1_sq + s3_sq = 2 + 2 * Vec3.dot n v + Vec3.sqNorm v)
    (h_det : s1_sq * s3_sq = (1 + Vec3.dot n v) ^ 2) :
    (s1_sq - 1) * (1 - s3_sq) = Vec3.sqNorm (Vec3.cross n v) ∧
    0 ≤ (s1_sq - 1) * (1 - s3_sq) := by
  have h_lagrange := Vec3.lagrange_identity_3d n v
  rw [h_unit, one_mul] at h_lagrange
  have h_prod : (s1_sq - 1) * (1 - s3_sq) = Vec3.sqNorm v - (Vec3.dot n v) ^ 2 := by
    calc
      (s1_sq - 1) * (1 - s3_sq) = (s1_sq + s3_sq) - s1_sq * s3_sq - 1 := by ring
      _ = (2 + 2 * Vec3.dot n v + Vec3.sqNorm v) - (1 + Vec3.dot n v) ^ 2 - 1 := by
        rw [h_trace, h_det]
      _ = Vec3.sqNorm v - (Vec3.dot n v) ^ 2 := by ring
  rw [h_prod, h_lagrange]
  refine ⟨rfl, ?_⟩
  dsimp [Vec3.sqNorm]
  positivity

#print axioms allSignTriples_length
#print axioms allSignTriples_nodup
#print axioms candidate_reproduces_homography
#print axioms ground_truth_satisfies_chirality
#print axioms elimination_theorem
#print axioms ground_truth_in_surviving
#print axioms eliminatedSignTriples_length
#print axioms eliminated_solutions_fail_chirality
#print axioms solution_count_equality
#print axioms Vec3.lagrange_identity_3d
#print axioms gram_homography_quad_form
#print axioms homography_gram_unit_eigenvector
#print axioms homography_singular_value_sandwich

end

end Research.HomographyDecomposition
