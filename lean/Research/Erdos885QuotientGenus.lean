import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Algebraic-Geometric Quotient Tower and Genus-2 Obstructions for Erdős Problem 885

This module formalizes the algebraic-geometric projection tower for the $6 \times 4$
rational-distance / factor-difference grid extension problem (Erdős Problem 885, Roadmap §6.3).

Given 6 distinct offsets $u : \text{Fin } 6 \to K$ over a commutative ring or field $K$,
the complete intersection curve $C \subset \mathbb{P}^6$ of 5 quadrics has affine chart
$$Z_m^2 = X + u_m \quad (m \in \text{Fin } 6).$$

We formalize and machine-check (with 0 `sorry` and standard axioms):
1. **The Quotient Projection Tower**:
   - Projection onto $\binom{6}{4} = 15$ quartic genus-1 elliptic models
     $E_{ijkl} : W^2 = (X+u_i)(X+u_j)(X+u_k)(X+u_l)$ (`quadric_projects_to_elliptic_four`).
   - Projection onto $\binom{6}{5} = 6$ **degree-5 genus-2 hyperelliptic curves**
     $C_5^{(r)} : W_r^2 = \prod_{m \ne r} (X + u_m)$ via $W_r = \prod_{m \ne r} Z_m$
     (`quadric_projects_to_genus2_five`).
   - Projection onto the **degree-6 genus-2 sextic hyperelliptic curve**
     $C_6 : W^2 = \prod_{m=0}^5 (X + u_m)$ via $W = \prod_{m=0}^5 Z_m$
     (`quadric_projects_to_genus2_six`).
   - Tower compatibility identities (`genus2_six_times_five_compatibility`,
     `genus2_six_mul_prod_five_syzygy`, and `genus2_five_prod_syzygy`):
     $W = Z_r \cdot W_r$, $W^2 = (X + u_r) \cdot W_r^2$, $W \cdot \prod_{r=0}^5 W_r = W^6$,
     and $\prod_{r=0}^5 W_r = W^5$.
2. **Birational Quartic Transformation from Sextic $C_6$ to Degree-5 Odd Weierstrass Model**:
   - Substituting $X = -u_0 + 1/T$ and $Y = W \cdot T^3$ (equivalently $W = Y / T^3$ for $T \ne 0$)
     transforms $W^2 = (X + u_0)\prod_{m=1}^5 (X + u_m)$ birationally into the degree-5 odd
     Weierstrass model
     $$Y^2 = \prod_{m=1}^5 \bigl(1 + (u_m - u_0) T\bigr)$$
     (`sextic_to_quintic_weierstrass`, `quintic_weierstrass_to_sextic`,
     `sextic_quintic_birational_iff`).
3. **Non-Vanishing Discriminants for Primitive $6 \times 4$ Grids**:
   - For the concrete grid offsets of Class 1 (59-smooth) and Class 2 (101-smooth),
     all 6 quintic curves $C_5^{(r)}$ and the sextic curve $C_6$ have pairwise distinct branch
     points and strictly non-zero polynomial discriminants (`class1FormB_offsets_injective`,
     `class2FormB_offsets_injective`, `class1FormB_sextic_disc_nonzero`,
     `class2FormB_sextic_disc_nonzero`).
4. **Richelot / Weierstrass Branch-Point Obstruction & Non-Weierstrass Column Lifts**:
   - Any Weierstrass branch point $W = 0$ on $C_6$ forces $Z_m = 0$ and $X = -u_m$ for a unique $m$,
     while the complementary quintic coordinate $W_m = \prod_{k \ne m} Z_k$ remains strictly
     non-zero (`unique_zero_coordinate_on_quadric_system`,
     `omitted_quintic_nonzero_at_branch_point`, `weierstrass_branch_point_obstruction`,
     `non_degenerate_grid_avoids_weierstrass_points`).
   - All 4 known columns of Class 1 and Class 2 lift to explicit non-Weierstrass integer points
     on the quadric system and all 7 genus-2 quotients (`class1FormB_known_columns_on_quadrics`,
     `class2FormB_known_columns_on_quadrics`).
-/

namespace Research.Erdos885QuotientGenus

open scoped BigOperators

/-! ## Section 1: The 6-Quadric System and Quotient Projection Tower -/

/-- A point `(X, Z)` lies on the affine 6-quadric system for offsets `u : Fin 6 → K`
if `Z m ^ 2 = X + u m` for all `m : Fin 6`. -/
abbrev OnQuadricSystem {K : Type*} [CommRing K] (u : Fin 6 → K) (X : K) (Z : Fin 6 → K) : Prop :=
  ∀ m : Fin 6, (Z m) ^ 2 = X + u m

/-- The 4-factor quartic elliptic curve projection `W = Z i * Z j * Z k * Z l`. -/
def ellipticFourW {K : Type*} [CommRing K] (Z : Fin 6 → K) (i j k l : Fin 6) : K :=
  Z i * Z j * Z k * Z l

/-- The 5-factor genus-2 hyperelliptic coordinate `W_r = ∏_{m ≠ r} Z_m` for omitted index `r`. -/
def genus2FiveW {K : Type*} [CommRing K] (Z : Fin 6 → K) (r : Fin 6) : K :=
  ∏ m ∈ Finset.univ.erase r, Z m

/-- The 5-factor degree-5 polynomial `P_r(X) = ∏_{m ≠ r} (X + u_m)` defining `C_5^(r)`. -/
def genus2FivePoly {K : Type*} [CommRing K] (u : Fin 6 → K) (r : Fin 6) (X : K) : K :=
  ∏ m ∈ Finset.univ.erase r, (X + u m)

/-- The 6-factor genus-2 sextic hyperelliptic coordinate `W = ∏_{m : Fin 6} Z_m`. -/
def genus2SixW {K : Type*} [CommRing K] (Z : Fin 6 → K) : K :=
  ∏ m : Fin 6, Z m

/-- The 6-factor degree-6 polynomial `P_6(X) = ∏_{m : Fin 6} (X + u_m)` defining `C_6`. -/
def genus2SixPoly {K : Type*} [CommRing K] (u : Fin 6 → K) (X : K) : K :=
  ∏ m : Fin 6, (X + u m)

/-- Projection onto any of the $\binom{6}{4} = 15$ genus-1 quartic elliptic models:
if $(X, Z)$ satisfies the quadric system, then $W = Z_i Z_j Z_k Z_l$ satisfies
$W^2 = (X + u_i)(X + u_j)(X + u_k)(X + u_l)$. -/
theorem quadric_projects_to_elliptic_four {K : Type*} [CommRing K]
    (u : Fin 6 → K) (X : K) (Z : Fin 6 → K) (hZ : OnQuadricSystem u X Z)
    (i j k l : Fin 6) :
    (ellipticFourW Z i j k l) ^ 2 = (X + u i) * (X + u j) * (X + u k) * (X + u l) := by
  unfold ellipticFourW
  calc
    (Z i * Z j * Z k * Z l) ^ 2
      = (Z i) ^ 2 * (Z j) ^ 2 * (Z k) ^ 2 * (Z l) ^ 2 := by ring
    _ = (X + u i) * (X + u j) * (X + u k) * (X + u l) := by
      rw [hZ i, hZ j, hZ k, hZ l]

/-- Projection onto any of the $\binom{6}{5} = 6$ degree-5 genus-2 hyperelliptic curves $C_5^{(r)}$:
if $(X, Z)$ satisfies the quadric system, then $W_r = \prod_{m \ne r} Z_m$ satisfies
$W_r^2 = \prod_{m \ne r} (X + u_m)$. -/
theorem quadric_projects_to_genus2_five {K : Type*} [CommRing K]
    (u : Fin 6 → K) (X : K) (Z : Fin 6 → K) (hZ : OnQuadricSystem u X Z)
    (r : Fin 6) :
    (genus2FiveW Z r) ^ 2 = genus2FivePoly u r X := by
  unfold genus2FiveW genus2FivePoly
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl ?_
  intro m _
  exact hZ m

/-- Projection onto the degree-6 genus-2 hyperelliptic curve $C_6$:
if $(X, Z)$ satisfies the quadric system, then $W = \prod_{m=0}^5 Z_m$ satisfies
$W^2 = \prod_{m=0}^5 (X + u_m)$. -/
theorem quadric_projects_to_genus2_six {K : Type*} [CommRing K]
    (u : Fin 6 → K) (X : K) (Z : Fin 6 → K) (hZ : OnQuadricSystem u X Z) :
    (genus2SixW Z) ^ 2 = genus2SixPoly u X := by
  unfold genus2SixW genus2SixPoly
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl ?_
  intro m _
  exact hZ m

/-- Compatibility between the sextic genus-2 quotient $C_6$ and the 6 quintic quotients $C_5^{(r)}$:
for every $r \in \text{Fin } 6$:
1. $W = Z_r \cdot W_r$,
2. $P_6(X) = (X + u_r) \cdot P_r(X)$,
3. $W^2 = (X + u_r) \cdot W_r^2$ on the quadric system. -/
theorem genus2_six_times_five_compatibility {K : Type*} [CommRing K]
    (u : Fin 6 → K) (X : K) (Z : Fin 6 → K) (hZ : OnQuadricSystem u X Z)
    (r : Fin 6) :
    genus2SixW Z = Z r * genus2FiveW Z r ∧
    genus2SixPoly u X = (X + u r) * genus2FivePoly u r X ∧
    (genus2SixW Z) ^ 2 = (X + u r) * (genus2FiveW Z r) ^ 2 := by
  have hW : genus2SixW Z = Z r * genus2FiveW Z r := by
    unfold genus2SixW genus2FiveW
    exact (Finset.mul_prod_erase Finset.univ Z (Finset.mem_univ r)).symm
  have hP : genus2SixPoly u X = (X + u r) * genus2FivePoly u r X := by
    unfold genus2SixPoly genus2FivePoly
    exact (Finset.mul_prod_erase Finset.univ (fun m => X + u m) (Finset.mem_univ r)).symm
  refine ⟨hW, hP, ?_⟩
  rw [quadric_projects_to_genus2_six u X Z hZ, hP, quadric_projects_to_genus2_five u X Z hZ]

/-- Universal product syzygy across all 6 quintic genus-2 coordinates and the sextic coordinate:
$W \cdot \prod_{r : \text{Fin } 6} W_r = W^6$. -/
theorem genus2_six_mul_prod_five_syzygy {K : Type*} [CommRing K] (Z : Fin 6 → K) :
    genus2SixW Z * (∏ r : Fin 6, genus2FiveW Z r) = (genus2SixW Z) ^ 6 := by
  have h_each : ∀ r : Fin 6, Z r * genus2FiveW Z r = genus2SixW Z := by
    intro r
    exact Finset.mul_prod_erase Finset.univ Z (Finset.mem_univ r)
  calc
    genus2SixW Z * (∏ r : Fin 6, genus2FiveW Z r)
      = (∏ r : Fin 6, Z r) * (∏ r : Fin 6, genus2FiveW Z r) := rfl
    _ = ∏ r : Fin 6, (Z r * genus2FiveW Z r) := by rw [← Finset.prod_mul_distrib]
    _ = ∏ _r : Fin 6, genus2SixW Z := Finset.prod_congr rfl (fun r _ => h_each r)
    _ = (genus2SixW Z) ^ 6 := by simp [Finset.prod_const, Fintype.card_fin]

/-- Over an integral domain, at any non-Weierstrass point ($W \ne 0$), the product of all 6
quintic coordinates equals the 5th power of the sextic coordinate:
$\prod_{r : \text{Fin } 6} W_r = W^5$. -/
theorem genus2_five_prod_syzygy {K : Type*} [CommRing K] [IsDomain K]
    (Z : Fin 6 → K) (hW : genus2SixW Z ≠ 0) :
    (∏ r : Fin 6, genus2FiveW Z r) = (genus2SixW Z) ^ 5 := by
  apply mul_left_cancel₀ hW
  calc
    genus2SixW Z * (∏ r : Fin 6, genus2FiveW Z r)
      = (genus2SixW Z) ^ 6 := genus2_six_mul_prod_five_syzygy Z
    _ = genus2SixW Z * (genus2SixW Z) ^ 5 := by ring

/-! ## Section 2: Birational Transformation of Sextic $C_6$ to Degree-5 Weierstrass Model -/

/-- The degree-5 odd Weierstrass polynomial associated to root `u 0` of `C_6`:
`Q(T) = ∏_{i : Fin 5} (1 + (u i.succ - u 0) * T)`. -/
def sexticWeierstrassQuinticPoly {K : Type*} [CommRing K] (u : Fin 6 → K) (T : K) : K :=
  ∏ i : Fin 5, (1 + (u i.succ - u 0) * T)

/-- Forward birational transformation from the degree-6 hyperelliptic curve
$W^2 = \prod_{m=0}^5 (X + u_m)$ to the degree-5 odd Weierstrass model
$Y^2 = \prod_{i=1}^5 (1 + (u_i - u_0) T)$ under $X = -u_0 + T^{-1}$ and $Y = W \cdot T^3$. -/
theorem sextic_to_quintic_weierstrass {K : Type*} [Field K]
    (u : Fin 6 → K) (X W T Y : K) (hT : T ≠ 0)
    (hX : X = -u 0 + T⁻¹) (hY : Y = W * T ^ 3)
    (hC6 : W ^ 2 = genus2SixPoly u X) :
    Y ^ 2 = sexticWeierstrassQuinticPoly u T := by
  have h0 : (X + u 0) * T = 1 := by
    rw [hX]
    field_simp [hT]
    ring
  have h_fac : ∀ i : Fin 5, (X + u i.succ) * T = 1 + (u i.succ - u 0) * T := by
    intro i
    rw [hX]
    field_simp [hT]
    ring
  have hT5 : (∏ _i : Fin 5, T) = T ^ 5 := by
    simp [Finset.prod_const, Fintype.card_fin]
  calc
    Y ^ 2 = W ^ 2 * T ^ 6 := by rw [hY]; ring
    _ = genus2SixPoly u X * (T * T ^ 5) := by rw [hC6]; ring
    _ = ((X + u 0) * ∏ i : Fin 5, (X + u i.succ)) * (T * ∏ _i : Fin 5, T) := by
      rw [genus2SixPoly, Fin.prod_univ_succ, hT5]
    _ = ((X + u 0) * T) * ((∏ i : Fin 5, (X + u i.succ)) * (∏ _i : Fin 5, T)) := by ring
    _ = 1 * ∏ i : Fin 5, ((X + u i.succ) * T) := by
      rw [h0, ← Finset.prod_mul_distrib]
    _ = sexticWeierstrassQuinticPoly u T := by
      rw [one_mul, sexticWeierstrassQuinticPoly]
      exact Finset.prod_congr rfl (fun i _ => h_fac i)

/-- Inverse birational transformation from the degree-5 odd Weierstrass model
$Y^2 = \prod_{i=1}^5 (1 + (u_i - u_0) T)$ back to the degree-6 hyperelliptic curve
$W^2 = \prod_{m=0}^5 (X + u_m)$ under $T = (X + u_0)^{-1}$ and $W = Y / T^3$. -/
theorem quintic_weierstrass_to_sextic {K : Type*} [Field K]
    (u : Fin 6 → K) (X W T Y : K) (hXu : X + u 0 ≠ 0)
    (hT : T = (X + u 0)⁻¹) (hW : W = Y / T ^ 3)
    (hQ : Y ^ 2 = sexticWeierstrassQuinticPoly u T) :
    W ^ 2 = genus2SixPoly u X := by
  have hT_ne : T ≠ 0 := by
    rw [hT]
    exact inv_ne_zero hXu
  have h0 : (X + u 0) * T = 1 := by
    rw [hT]
    exact mul_inv_cancel₀ hXu
  have h_fac : ∀ i : Fin 5, 1 + (u i.succ - u 0) * T = (X + u i.succ) * T := by
    intro i
    rw [hT]
    field_simp [hXu]
    ring
  have hT5 : (∏ _i : Fin 5, T) = T ^ 5 := by
    simp [Finset.prod_const, Fintype.card_fin]
  have h_six : (X + u 0) * (∏ i : Fin 5, (X + u i.succ)) = genus2SixPoly u X :=
    (Fin.prod_univ_succ (fun m : Fin 6 => X + u m)).symm
  have hQ_expanded : Y ^ 2 = genus2SixPoly u X * T ^ 6 := by
    calc
      Y ^ 2 = sexticWeierstrassQuinticPoly u T := hQ
      _ = 1 * ∏ i : Fin 5, (1 + (u i.succ - u 0) * T) := by
        rw [one_mul, sexticWeierstrassQuinticPoly]
      _ = ((X + u 0) * T) * ∏ i : Fin 5, ((X + u i.succ) * T) := by
        rw [h0]
        congr 1
        exact Finset.prod_congr rfl (fun i _ => h_fac i)
      _ = ((X + u 0) * T) * ((∏ i : Fin 5, (X + u i.succ)) * (∏ _i : Fin 5, T)) := by
        rw [Finset.prod_mul_distrib]
      _ = ((X + u 0) * ∏ i : Fin 5, (X + u i.succ)) * (T * T ^ 5) := by
        rw [hT5]
        ring
      _ = genus2SixPoly u X * T ^ 6 := by
        rw [h_six]
        ring
  calc
    W ^ 2 = Y ^ 2 / T ^ 6 := by rw [hW]; ring
    _ = (genus2SixPoly u X * T ^ 6) / T ^ 6 := by rw [hQ_expanded]
    _ = genus2SixPoly u X := by field_simp [hT_ne]

/-- Biconditional birational equivalence between the degree-6 hyperelliptic model $C_6$
away from the branch point $X = -u_0$ and the degree-5 odd Weierstrass model. -/
theorem sextic_quintic_birational_iff {K : Type*} [Field K]
    (u : Fin 6 → K) (T Y : K) (hT : T ≠ 0) :
    (Y / T ^ 3) ^ 2 = genus2SixPoly u (-u 0 + T⁻¹) ↔
      Y ^ 2 = sexticWeierstrassQuinticPoly u T := by
  constructor
  · intro hC6
    exact sextic_to_quintic_weierstrass u (-u 0 + T⁻¹) (Y / T ^ 3) T Y hT rfl
      (by field_simp [hT]) hC6
  · intro hQ
    have hXu : (-u 0 + T⁻¹) + u 0 ≠ 0 := by
      have h_eq : (-u 0 + T⁻¹) + u 0 = T⁻¹ := by ring
      rw [h_eq]
      exact inv_ne_zero hT
    have hT_inv : T = ((-u 0 + T⁻¹) + u 0)⁻¹ := by
      field_simp [hT]
      ring
    exact quintic_weierstrass_to_sextic u (-u 0 + T⁻¹) (Y / T ^ 3) T Y hXu hT_inv rfl hQ

/-! ## Section 3: Richelot / Branch-Point Obstruction & Non-Degenerate Lifts -/

/-- If the offsets `u : Fin 6 → K` are pairwise distinct, then at most one coordinate `Z_m`
can vanish at any point `(X, Z)` on the 6-quadric system. -/
theorem unique_zero_coordinate_on_quadric_system {K : Type*} [CommRing K]
    (u : Fin 6 → K) (hu : Function.Injective u)
    (X : K) (Z : Fin 6 → K) (hZ : OnQuadricSystem u X Z)
    {a b : Fin 6} (ha : Z a = 0) (hb : Z b = 0) :
    a = b := by
  have hZa := hZ a
  have hZb := hZ b
  rw [ha, sq, mul_zero] at hZa
  rw [hb, sq, mul_zero] at hZb
  have h_eq : u a = u b := by linear_combination -hZa + hZb
  exact hu h_eq

/-- If `(X, Z)` lies on the quadric system with `Z r = 0`, and `u` is injective over an
integral domain `K`, then every other coordinate `Z m` (`m ≠ r`) is non-zero, and hence
the omitted-`r` quintic genus-2 coordinate `W_r = ∏_{m ≠ r} Z_m` is strictly non-zero! -/
theorem omitted_quintic_nonzero_at_branch_point {K : Type*} [CommRing K] [IsDomain K]
    (u : Fin 6 → K) (hu : Function.Injective u)
    (X : K) (Z : Fin 6 → K) (hZ : OnQuadricSystem u X Z)
    (r : Fin 6) (hr : Z r = 0) :
    genus2FiveW Z r ≠ 0 := by
  unfold genus2FiveW
  rw [Finset.prod_ne_zero_iff]
  intro m hm
  have hmr : m ≠ r := (Finset.mem_erase.mp hm).1
  intro hm_zero
  exact hmr (unique_zero_coordinate_on_quadric_system u hu X Z hZ hm_zero hr)

/-- Weierstrass Branch-Point Obstruction:
Over an integral domain $K$, a point $(X, Z)$ on the quadric system maps to a Weierstrass
branch point $W = 0$ on the sextic curve $C_6$ if and only if $X = -u_m$ for some $m \in \text{Fin } 6$.
Consequently, any non-degenerate grid extension where $X + u_m \ne 0$ for all $m$ strictly
avoids all 6 finite Weierstrass points of $C_6$ and all 5 finite Weierstrass points of each $C_5^{(r)}$. -/
theorem weierstrass_branch_point_obstruction {K : Type*} [CommRing K] [IsDomain K]
    (u : Fin 6 → K) (X : K) (Z : Fin 6 → K) (hZ : OnQuadricSystem u X Z) :
    genus2SixW Z = 0 ↔ ∃ m : Fin 6, X + u m = 0 := by
  unfold genus2SixW
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨m, _, hm⟩
    refine ⟨m, ?_⟩
    rw [← hZ m, hm, sq, mul_zero]
  · rintro ⟨m, hm⟩
    refine ⟨m, Finset.mem_univ m, ?_⟩
    have hZm : (Z m) ^ 2 = 0 := by rw [hZ m, hm]
    exact sq_eq_zero_iff.mp hZm

/-- Non-Degenerate Grid Extension Avoids All Weierstrass Points:
Over any integral domain $K$, if $X + u_m \ne 0$ for all $m \in \text{Fin } 6$, then for any
solution $(X, Z)$ of the quadric system, both the sextic coordinate $W$ and all 6 quintic
coordinates $W_r$ are strictly non-zero. -/
theorem non_degenerate_grid_avoids_weierstrass_points {K : Type*} [CommRing K] [IsDomain K]
    (u : Fin 6 → K) (X : K) (Z : Fin 6 → K) (hZ : OnQuadricSystem u X Z)
    (hne : ∀ m : Fin 6, X + u m ≠ 0) :
    genus2SixW Z ≠ 0 ∧ ∀ r : Fin 6, genus2FiveW Z r ≠ 0 := by
  have hZ_ne : ∀ m : Fin 6, Z m ≠ 0 := by
    intro m hm
    apply hne m
    rw [← hZ m, hm, sq, mul_zero]
  refine ⟨?_, ?_⟩
  · unfold genus2SixW
    exact Finset.prod_ne_zero_iff.mpr (fun m _ => hZ_ne m)
  · intro r
    unfold genus2FiveW
    exact Finset.prod_ne_zero_iff.mpr (fun m _ => hZ_ne m)

/-- Distinctness of the 5 affine branch points of the birational degree-5 Weierstrass model:
if `u : Fin 6 → K` is injective, then the 5 nonzero branch-point coefficients `u i.succ - u 0`
are pairwise distinct and non-zero. -/
theorem birational_quintic_coefficients_distinct {K : Type*} [CommRing K]
    (u : Fin 6 → K) (hu : Function.Injective u) :
    (∀ i : Fin 5, u i.succ - u 0 ≠ 0) ∧
    Function.Injective (fun i : Fin 5 => u i.succ - u 0) := by
  refine ⟨?_, ?_⟩
  · intro i h_sub
    have h_eq : u i.succ = u 0 := sub_eq_zero.mp h_sub
    exact Fin.succ_ne_zero i (hu h_eq)
  · intro i j hij
    have h_eq : u i.succ = u j.succ := by linear_combination hij
    exact Fin.succ_inj.mp (hu h_eq)

/-! ## Section 4: Concrete Verification for Primitive $6 \times 4$ Grids (Class 1 & Class 2) -/

/-- Class 1 (59-smooth) Form B row offsets $u_m = d_m^2$ for
$d = (6720, 15855, 26880, 45440, 69510, 129290)$. -/
def class1FormB_U : Fin 6 → ℤ :=
  ![6720 ^ 2, 15855 ^ 2, 26880 ^ 2, 45440 ^ 2, 69510 ^ 2, 129290 ^ 2]

/-- Class 1 (59-smooth) Form B known columns $v_j = 4 N_j$. -/
def class1FormB_V : Fin 4 → ℤ :=
  ![0, 4 * 349102656, 4 * 1034586000, 4 * 4883112000]

/-- Explicit positive integer square roots $Z_{j, m}$ satisfying $Z_{j, m}^2 = v_j + u_m$
for all 4 columns $j \in \text{Fin } 4$ and 6 rows $m \in \text{Fin } 6$ in Class 1 Form B. -/
def class1FormB_Z : Fin 4 → Fin 6 → ℤ :=
  ![![6720, 15855, 26880, 45440, 69510, 129290],
    ![37968, 40593, 46032, 58832, 78918, 134582],
    ![64680, 66255, 69720, 78760, 94710, 144410],
    ![139920, 140655, 142320, 146960, 156090, 190390]]

/-- Class 2 (101-smooth) Form B row offsets $u_m = d_m^2$ for
$d = (2988, 4356, 5787, 11164, 17046, 23948)$. -/
def class2FormB_U : Fin 6 → ℤ :=
  ![2988 ^ 2, 4356 ^ 2, 5787 ^ 2, 11164 ^ 2, 17046 ^ 2, 23948 ^ 2]

/-- Class 2 (101-smooth) Form B known columns $v_j = 4 N_j$. -/
def class2FormB_V : Fin 4 → ℤ :=
  ![0, 4 * 4148640, 4 * 34418880, 4 * 300736800]

/-- Explicit positive integer square roots $Z_{j, m}$ satisfying $Z_{j, m}^2 = v_j + u_m$
for all 4 columns $j \in \text{Fin } 4$ and 6 rows $m \in \text{Fin } 6$ in Class 2 Form B. -/
def class2FormB_Z : Fin 4 → Fin 6 → ℤ :=
  ![![2988, 4356, 5787, 11164, 17046, 23948],
    ![5052, 5964, 7077, 11884, 17526, 24292],
    ![12108, 12516, 13083, 16196, 20694, 26668],
    ![34812, 34956, 35163, 36436, 38646, 42148]]

/-- All 6 branch points of Class 1 Form B are pairwise distinct (`Function.Injective`). -/
theorem class1FormB_offsets_injective : Function.Injective class1FormB_U := by
  decide

/-- All 6 branch points of Class 2 Form B are pairwise distinct (`Function.Injective`). -/
theorem class2FormB_offsets_injective : Function.Injective class2FormB_U := by
  decide

/-- The polynomial discriminant product $\prod_{i < j} (u_j - u_i)$ of the sextic curve $C_6$
and all 6 quintic curves $C_5^{(r)}$ is strictly non-zero for Class 1 Form B. -/
theorem class1FormB_sextic_disc_nonzero :
    ∀ i j : Fin 6, i ≠ j → class1FormB_U i - class1FormB_U j ≠ 0 := by
  decide

/-- The polynomial discriminant product $\prod_{i < j} (u_j - u_i)$ of the sextic curve $C_6$
and all 6 quintic curves $C_5^{(r)}$ is strictly non-zero for Class 2 Form B. -/
theorem class2FormB_sextic_disc_nonzero :
    ∀ i j : Fin 6, i ≠ j → class2FormB_U i - class2FormB_U j ≠ 0 := by
  decide

lemma class1FormB_quadric_check :
    ∀ j : Fin 4, ∀ m : Fin 6, (class1FormB_Z j m) ^ 2 = class1FormB_V j + class1FormB_U m := by
  decide

lemma class1FormB_sum_nonzero :
    ∀ j : Fin 4, ∀ m : Fin 6, class1FormB_V j + class1FormB_U m ≠ 0 := by
  decide

lemma class2FormB_quadric_check :
    ∀ j : Fin 4, ∀ m : Fin 6, (class2FormB_Z j m) ^ 2 = class2FormB_V j + class2FormB_U m := by
  decide

lemma class2FormB_sum_nonzero :
    ∀ j : Fin 4, ∀ m : Fin 6, class2FormB_V j + class2FormB_U m ≠ 0 := by
  decide

/-- All 4 known columns of Class 1 Form B satisfy the 6-quadric system $Z_{j, m}^2 = v_j + u_m$
and project onto non-Weierstrass integer points ($W \ne 0$ and $W_r \ne 0$) on all 7 genus-2
quotients ($C_6$ and $C_5^{(0)}, \dots, C_5^{(5)}$). -/
theorem class1FormB_known_columns_on_quadrics :
    ∀ j : Fin 4,
      OnQuadricSystem class1FormB_U (class1FormB_V j) (class1FormB_Z j) ∧
      (genus2SixW (class1FormB_Z j)) ^ 2 = genus2SixPoly class1FormB_U (class1FormB_V j) ∧
      genus2SixW (class1FormB_Z j) ≠ 0 ∧
      ∀ r : Fin 6,
        (genus2FiveW (class1FormB_Z j) r) ^ 2 =
          genus2FivePoly class1FormB_U r (class1FormB_V j) ∧
        genus2FiveW (class1FormB_Z j) r ≠ 0 := by
  intro j
  have hQ : OnQuadricSystem class1FormB_U (class1FormB_V j) (class1FormB_Z j) :=
    class1FormB_quadric_check j
  have hne : ∀ m : Fin 6, class1FormB_V j + class1FormB_U m ≠ 0 :=
    class1FormB_sum_nonzero j
  obtain ⟨hW6_ne, hW5_ne⟩ :=
    non_degenerate_grid_avoids_weierstrass_points class1FormB_U (class1FormB_V j)
      (class1FormB_Z j) hQ hne
  refine ⟨hQ, quadric_projects_to_genus2_six class1FormB_U (class1FormB_V j) (class1FormB_Z j) hQ,
    hW6_ne, ?_⟩
  intro r
  exact ⟨quadric_projects_to_genus2_five class1FormB_U (class1FormB_V j) (class1FormB_Z j) hQ r,
    hW5_ne r⟩

/-- All 4 known columns of Class 2 Form B satisfy the 6-quadric system $Z_{j, m}^2 = v_j + u_m$
and project onto non-Weierstrass integer points ($W \ne 0$ and $W_r \ne 0$) on all 7 genus-2
quotients ($C_6$ and $C_5^{(0)}, \dots, C_5^{(5)}$). -/
theorem class2FormB_known_columns_on_quadrics :
    ∀ j : Fin 4,
      OnQuadricSystem class2FormB_U (class2FormB_V j) (class2FormB_Z j) ∧
      (genus2SixW (class2FormB_Z j)) ^ 2 = genus2SixPoly class2FormB_U (class2FormB_V j) ∧
      genus2SixW (class2FormB_Z j) ≠ 0 ∧
      ∀ r : Fin 6,
        (genus2FiveW (class2FormB_Z j) r) ^ 2 =
          genus2FivePoly class2FormB_U r (class2FormB_V j) ∧
        genus2FiveW (class2FormB_Z j) r ≠ 0 := by
  intro j
  have hQ : OnQuadricSystem class2FormB_U (class2FormB_V j) (class2FormB_Z j) :=
    class2FormB_quadric_check j
  have hne : ∀ m : Fin 6, class2FormB_V j + class2FormB_U m ≠ 0 :=
    class2FormB_sum_nonzero j
  obtain ⟨hW6_ne, hW5_ne⟩ :=
    non_degenerate_grid_avoids_weierstrass_points class2FormB_U (class2FormB_V j)
      (class2FormB_Z j) hQ hne
  refine ⟨hQ, quadric_projects_to_genus2_six class2FormB_U (class2FormB_V j) (class2FormB_Z j) hQ,
    hW6_ne, ?_⟩
  intro r
  exact ⟨quadric_projects_to_genus2_five class2FormB_U (class2FormB_V j) (class2FormB_Z j) hQ r,
    hW5_ne r⟩

#print axioms quadric_projects_to_elliptic_four
#print axioms quadric_projects_to_genus2_five
#print axioms quadric_projects_to_genus2_six
#print axioms genus2_six_times_five_compatibility
#print axioms genus2_six_mul_prod_five_syzygy
#print axioms genus2_five_prod_syzygy
#print axioms sextic_to_quintic_weierstrass
#print axioms quintic_weierstrass_to_sextic
#print axioms sextic_quintic_birational_iff
#print axioms unique_zero_coordinate_on_quadric_system
#print axioms omitted_quintic_nonzero_at_branch_point
#print axioms weierstrass_branch_point_obstruction
#print axioms non_degenerate_grid_avoids_weierstrass_points
#print axioms birational_quintic_coefficients_distinct
#print axioms class1FormB_known_columns_on_quadrics
#print axioms class2FormB_known_columns_on_quadrics

end Research.Erdos885QuotientGenus
