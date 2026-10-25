import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.RingHoms
import Research.Erdos885MumfordChabauty

/-!
# Rank-1 Chabauty–Coleman + Mordell–Weil sieve certificate for the quintic `C₅` (Erdős 885 lane)

This module treats the genus-2 curve
$$C_5 : w^2 = f(x) = x^5 + 89x^4 + 2796x^3 + 35704x^2 + 123200x$$
(`class1QuinticC5` in `Research.Erdos885MumfordChabauty`) and reduces the statement
"`C₅(ℚ) = {∞, (0,0)}`" to explicit, named hypotheses, checking every finite computation in Lean.

## What is proved outright (0 `sorry`, `decide +kernel` only, no `native_decide`)

* `mumfordD_relation`, `mumfordD_a_no_rational_root`: `D = (x² + 8x + 32, 136x + 272)` is a
  degree-2 Mumford divisor over `ℚ` (`x² + 8x + 32 ∣ f − b²`) whose support is not rational.
* `c5F17_card_points`: `#C₅(𝔽₁₇) = 22` (projective, one point at infinity), and
  `c5F17_weierstrass`: the affine Weierstrass points over `𝔽₁₇` are `x ∈ {0, 10, 11, 12, 14}`.
* `c5_count_F289`: `#C₅(𝔽₁₇²) = 350` (with `𝔽₂₈₉ = 𝔽₁₇[√3]`), and `c5_jacobian_count_F17`:
  `(22² + 350)/2 − 17 = 400`, the standard genus-2 formula for `#J(𝔽₁₇)`. The same counts at
  `p = 13, 29, 41` give `148, 1042, 2000` (`c5_jacobian_counts_13_29_41`); `gcd(148, 1042) = 2`.
* `mumfordD_mod17`: `D` reduces mod 17 to `(x − 12)(x − 14), b ≡ 0`, i.e. to the 2-torsion class
  `[W₁₂ + W₁₄ − 2∞]`.
* `redPt17_onC5`: reduction `C₅(ℚ) → C₅(𝔽₁₇)` (through `ℤ_[17]`) is well defined.
* `padic_unique_zero_of_unit_linear`: a Strassmann-type lemma: `c·s + 17·tail(s)` with `c` a unit and
  `tail` 1-Lipschitz has at most one zero in `ℤ_[17]`.
* `ColemanDiskCertificate.eq_of_reduction_eq`: a disk certificate pins down the unique rational
  point in its residue disk.
* `c5_rational_points_of_rank_one`: **main theorem.** Given a `C5Rank1JacobianInput` (the
  Jacobian facts below) and Coleman disk certificates at `∞` and at `(0,0)`, the rational points of
  `C₅` are exactly `∞` and `(0,0)`. The single-prime Mordell–Weil sieve at `p = 17` is proved here:
  every rational point reduces into the residue disks of `∞` or `(0,0)`.

## What is assumed (explicit hypotheses, never hidden)

`C5Rank1JacobianInput` bundles:
* `mw_gen`: `J(ℚ) = ℤ·G ⊕ ⟨T⟩`, `T = [(0,0) − ∞]` (**rank ≤ 1** and torsion `⊆ ⟨T⟩`). The rank
  upper bound needs a 2-descent (Magma/Sage), which is not available here. Torsion `⊆ ℤ/2` and rank
  `≥ 1` are supported numerically: `gcd #J(𝔽_p) = 2` and `D` has order 74 in `J(𝔽₁₃)`.
* `D_mul`, `m_coprime`: `D = m·G (+T)` with `gcd(m, 10) = 1` (2- and 5-saturation of `⟨D, T⟩`).
  Numerically: `J(𝔽₁₇)[2] ≅ (ℤ/2)⁴` is the whole 2-Sylow subgroup and `D₁₇ ∉ {0, T₁₇}`. The 5-Sylow
  subgroup of `J(𝔽₄₁)` has order 125 and `D₄₁` has order 250.
* Standard facts about the Jacobian of the smooth genus-2 curve `C₅/𝔽₁₇` and reduction:
  `card_H` (`#J(𝔽₁₇) = (N₁² + N₂)/2 − q`), `ajp_infty`, `ajp_inv` (`div(x − x_P)`), `ajp_div_y`
  (`div(y)`), `ajp_rigid` (on a genus-2 curve two effective degree-2 divisors are linearly equivalent
  only if they are equal or both canonical), `aj_red` (reduction commutes with Abel–Jacobi) and
  `red_D` (reduction of the Mumford representation of `D`).

`ColemanDiskCertificate` is the analytic input: on the residue disk the Coleman integral of the
annihilating differential `ω_ann` (`∫_D ω_ann = 0`) is, after rescaling, `c·s + 17·tail(s)` with
`c ∈ ℤ_[17]ˣ`, and it vanishes at every rational point of the disk. Under rank 1 the expansion and
vanishing are standard Coleman theory. Only `IsUnit c` depends on the curve. Numerically, from
tiny integrals on `2D, 4D, 6D` (all reducing into the disk of `(0,0)`, consistent to `17⁶`):
`∫_{2D} dx/y = 17·u₀`, `∫_{2D} x dx/y = 17²·u₁` with `u₀ ≡ 10`, `u₁ ≡ 16 (mod 17)`. So
`ω_ann ∝ 17u₁·dx/y − u₀·x dx/y`, giving `c ≡ 2u₀ ≡ 3` at `∞` and `c ≡ u₁/61600 ≡ 15` at `(0,0)`,
both units. These numerics live outside Lean (see `work/885/log.md`).

## Provenance warning

`C₅` is **not** one of the genus-2 quotients `W² = ∏_{m≠r}(X + u_m)` of the Class 1 grid curve built
in `Erdos885QuotientGenus`: those split completely over `ℚ`, while `f = x · q₅(x)` with `q₅`
irreducible over `ℚ`. So `J(ℚ)[2] ≅ ℤ/2` here, against `(ℤ/2)⁴` for every tower quotient, and the
Weierstrass-point Galois module is a `ℚ`-isomorphism invariant. This module proves facts about
`C₅` as stated in the roadmap. Its bearing on Erdős 885 (`k = 5`) is not established.
-/

namespace Research.Erdos885C5Chabauty

open Research.Erdos885MumfordChabauty

instance fact_prime_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-! ## 1. The curve over an arbitrary commutative ring -/

/-- The quintic `f(x) = x⁵ + 89x⁴ + 2796x³ + 35704x² + 123200x` over any commutative ring. -/
def c5 {R : Type*} [CommRing R] (x : R) : R :=
  x ^ 5 + 89 * x ^ 4 + 2796 * x ^ 3 + 35704 * x ^ 2 + 123200 * x

/-- `c5` agrees with `class1QuinticC5` on integers. -/
theorem c5_intCast (x : ℤ) : c5 (x : ℚ) = (class1QuinticC5 x : ℚ) := by
  unfold c5 class1QuinticC5; push_cast; ring

/-- `c5` commutes with ring homomorphisms. -/
theorem c5_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (x : R) :
    φ (c5 x) = c5 (φ x) := by
  simp [c5, map_add, map_mul, map_pow, map_ofNat]

/-- Points of the smooth projective model of `C₅` over `R`: `none` is the unique point at infinity
(the model is odd degree), and `some (x, w)` is an affine point with `w² = f(x)`. -/
def OnC5 {R : Type*} [CommRing R] : Option (R × R) → Prop
  | none => True
  | some (x, w) => w ^ 2 = c5 x

instance {R : Type*} [CommRing R] [DecidableEq R] : DecidablePred (OnC5 (R := R)) := fun P =>
  match P with
  | none => isTrue trivial
  | some (x, w) => (inferInstance : Decidable (w ^ 2 = c5 x))

/-- The hyperelliptic involution `ι(x, w) = (x, −w)`, `ι(∞) = ∞`. -/
def hypInv {R : Type*} [CommRing R] : Option (R × R) → Option (R × R)
  | none => none
  | some (x, w) => some (x, -w)

/-- The two known rational points `∞` and `(0, 0)` lie on `C₅`. -/
theorem onC5_known : OnC5 (none : Option (ℚ × ℚ)) ∧ OnC5 (some ((0 : ℚ), (0 : ℚ))) := by
  refine ⟨trivial, ?_⟩
  show (0 : ℚ) ^ 2 = c5 0
  simp [c5]

/-! ## 2. The degree-2 Mumford divisor `D` over `ℚ` -/

/-- `D = (a, b)` with `a = x² + 8x + 32`, `b = 136x + 272` is a Mumford divisor:
`f − b² = a · (x³ + 81x² + 2116x − 2312)`. -/
theorem mumfordD_relation (x : ℚ) :
    c5 x - (136 * x + 272) ^ 2 = (x ^ 2 + 8 * x + 32) * (x ^ 3 + 81 * x ^ 2 + 2116 * x - 2312) := by
  unfold c5; ring

/-- `a = x² + 8x + 32 = (x + 4)² + 16` has no rational root, so `D` is not a sum of two rational
points; it is the class of a pair of conjugate points over `ℚ(i)`. -/
theorem mumfordD_a_no_rational_root (x : ℚ) : x ^ 2 + 8 * x + 32 ≠ 0 := by
  nlinarith [sq_nonneg (x + 4)]

/-! ## 3. Finite-field certificates at `p = 17` (and point counts at `13, 29, 41`) -/

/-- `#C₅(𝔽₁₇) = 22` (21 affine points plus `∞`). -/
theorem c5F17_card_points :
    (Finset.univ.filter (fun P : Option (ZMod 17 × ZMod 17) => OnC5 P)).card = 22 := by
  decide +kernel

/-- The affine Weierstrass points of `C₅` over `𝔽₁₇`: `f` splits with roots `0, 10, 11, 12, 14`. -/
theorem c5F17_weierstrass (x : ZMod 17) :
    c5 x = 0 ↔ x = 0 ∨ x = 10 ∨ x = 11 ∨ x = 12 ∨ x = 14 := by
  revert x; decide +kernel

/-- Reduction of `D` mod 17: `a ≡ (x − 12)(x − 14)` and `b ≡ 0`, so `D₁₇ = [W₁₂ + W₁₄ − 2∞]`. -/
theorem mumfordD_mod17 :
    (∀ x : ZMod 17, x ^ 2 + 8 * x + 32 = (x - 12) * (x - 14)) ∧
      (136 : ZMod 17) = 0 ∧ (272 : ZMod 17) = 0 := by
  refine ⟨?_, by decide, by decide⟩
  decide +kernel

/-- `f(x) mod p`, computed on natural numbers (for kernel-friendly point counts). -/
def fNat (p x : ℕ) : ℕ := (x ^ 5 + 89 * x ^ 4 + 2796 * x ^ 3 + 35704 * x ^ 2 + 123200 * x) % p

/-- `#C₅(𝔽_p)` for the projective model (one point at infinity). -/
def countF (p : ℕ) : ℕ :=
  1 + ((List.range p).map fun x => ((List.range p).filter fun y => y * y % p == fNat p x).length).sum

/-- Multiplication in `𝔽_p[√d]` on pairs of residues. -/
def mulQ (p d : ℕ) (u v : ℕ × ℕ) : ℕ × ℕ :=
  ((u.1 * v.1 + d * (u.2 * v.2)) % p, (u.1 * v.2 + u.2 * v.1) % p)

/-- `f(z)` for `z ∈ 𝔽_p[√d]`. -/
def fQ (p d : ℕ) (z : ℕ × ℕ) : ℕ × ℕ :=
  let z2 := mulQ p d z z
  let z3 := mulQ p d z2 z
  let z4 := mulQ p d z3 z
  let z5 := mulQ p d z4 z
  ((z5.1 + 89 * z4.1 + 2796 * z3.1 + 35704 * z2.1 + 123200 * z.1) % p,
    (z5.2 + 89 * z4.2 + 2796 * z3.2 + 35704 * z2.2 + 123200 * z.2) % p)

/-- Number of points of `C₅` over `𝔽_{p²} = 𝔽_p[√d]` above `x = z` (`d` a non-residue). A nonzero
`u ∈ 𝔽_{p²}` is a square iff its norm `u₁² − d u₂²` is a square in `𝔽_p` (Euler's criterion). -/
def ptsAbove (p d : ℕ) (z : ℕ × ℕ) : ℕ :=
  let v := fQ p d z
  if v = (0, 0) then 1
  else if ((v.1 * v.1 + (p - d) * (v.2 * v.2 % p)) % p) ^ ((p - 1) / 2) % p = 1 then 2 else 0

/-- `#C₅(𝔽_{p²})` for the projective model. -/
def countF2 (p d : ℕ) : ℕ :=
  1 + ((List.range p).map fun a => ((List.range p).map fun b => ptsAbove p d (a, b)).sum).sum

/-- `#J(𝔽_p) = (N₁² + N₂)/2 − p`, the standard genus-2 formula (from the L-polynomial). -/
def jacCount (p d : ℕ) : ℕ := (countF p ^ 2 + countF2 p d) / 2 - p

/-- The `ℕ`-level count at `p = 17` agrees with the `ZMod 17` point count. -/
theorem c5_countF_17 : countF 17 = 22 := by decide +kernel

/-- `#C₅(𝔽₂₈₉) = 350`, with `𝔽₂₈₉ = 𝔽₁₇[√3]` (3 is a non-residue mod 17). -/
theorem c5_count_F289 : countF2 17 3 = 350 := by decide +kernel

/-- `#J(𝔽₁₇) = (22² + 350)/2 − 17 = 400 = 2⁴·5²`. -/
theorem c5_jacobian_count_F17 : jacCount 17 3 = 400 := by decide +kernel

/-- `#J(𝔽₁₃) = 148`, `#J(𝔽₂₉) = 1042`, `#J(𝔽₄₁) = 2000` (non-residues 2, 2, 3). Since
`gcd(148, 1042) = 2` and torsion injects into `J(𝔽_p)` for odd good `p`, `#J(ℚ)_tors ∣ 2`. -/
theorem c5_jacobian_counts_13_29_41 :
    jacCount 13 2 = 148 ∧ jacCount 29 2 = 1042 ∧ jacCount 41 3 = 2000 ∧
      Nat.gcd 148 1042 = 2 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by norm_num⟩

/-! ## 4. Reduction `C₅(ℚ) → C₅(𝔽₁₇)` through `ℤ_[17]` -/

/-- Reduction of a `17`-integral rational number mod 17 (junk value `0` otherwise). -/
noncomputable def redQ17 (x : ℚ) : ZMod 17 :=
  if h : ‖(x : ℚ_[17])‖ ≤ 1 then PadicInt.toZMod (⟨x, h⟩ : ℤ_[17]) else 0

/-- Reduction of points: affine points with `17`-integral `x` go to `(x̄, w̄)`, all others to `∞`. -/
noncomputable def redPt17 : Option (ℚ × ℚ) → Option (ZMod 17 × ZMod 17)
  | none => none
  | some (x, w) => if ‖(x : ℚ_[17])‖ ≤ 1 then some (redQ17 x, redQ17 w) else none

theorem c5_ratCast (x : ℚ) : ((c5 x : ℚ) : ℚ_[17]) = c5 (x : ℚ_[17]) := by
  simp [c5]

/-- The reduction of a rational point of `C₅` is a point of `C₅(𝔽₁₇)`. -/
theorem redPt17_onC5 {P : Option (ℚ × ℚ)} (hP : OnC5 P) : OnC5 (redPt17 P) := by
  match P, hP with
  | none, _ => exact trivial
  | some (x, w), hP =>
    have hP' : w ^ 2 = c5 x := hP
    by_cases hx : ‖(x : ℚ_[17])‖ ≤ 1
    · set X : ℤ_[17] := ⟨x, hx⟩ with hXdef
      have hcX : ((c5 X : ℤ_[17]) : ℚ_[17]) = c5 (x : ℚ_[17]) := by
        have := c5_map (PadicInt.Coe.ringHom (p := 17)) X
        exact this
      have hw2 : ((w : ℚ_[17])) ^ 2 = c5 (x : ℚ_[17]) := by
        rw [← c5_ratCast, ← hP']; push_cast; ring
      have hw : ‖(w : ℚ_[17])‖ ≤ 1 := by
        have h1 : ‖(w : ℚ_[17])‖ ^ 2 ≤ 1 := by
          rw [← norm_pow, hw2, ← hcX]; exact PadicInt.norm_le_one _
        nlinarith [norm_nonneg (w : ℚ_[17])]
      set W : ℤ_[17] := ⟨w, hw⟩ with hWdef
      have hWX : W ^ 2 = c5 X := by
        apply PadicInt.ext
        rw [hcX, ← hw2, PadicInt.coe_pow]
      have hred : redPt17 (some (x, w)) = some (PadicInt.toZMod X, PadicInt.toZMod W) := by
        show (if ‖(x : ℚ_[17])‖ ≤ 1 then some (redQ17 x, redQ17 w) else none) = _
        rw [if_pos hx]
        unfold redQ17
        rw [dif_pos hx, dif_pos hw]
      rw [hred]
      show (PadicInt.toZMod W) ^ 2 = c5 (PadicInt.toZMod X)
      rw [← map_pow, hWX, c5_map]
    · show OnC5 (if ‖(x : ℚ_[17])‖ ≤ 1 then some (redQ17 x, redQ17 w) else none)
      rw [if_neg hx]
      exact trivial

theorem redPt17_zero : redPt17 (some ((0 : ℚ), (0 : ℚ))) = some (0, 0) := by
  have h0 : redQ17 0 = 0 := by
    have hn : ‖((0 : ℚ) : ℚ_[17])‖ ≤ 1 := by simp
    have h0' : (0 : ℤ_[17]) = ⟨((0 : ℚ) : ℚ_[17]), hn⟩ := PadicInt.ext (by simp)
    unfold redQ17
    rw [dif_pos hn, ← h0', map_zero]
  simp [redPt17, h0]

/-! ## 5. Strassmann-type uniqueness in `ℤ_[p]` -/

/-- If `c` is a `p`-adic unit and `tail` is 1-Lipschitz, then `s ↦ c·s + p·tail(s)` has at most one
zero in `ℤ_[p]`. This is the residue-disk zero count used in Chabauty–Coleman. -/
theorem padic_unique_zero_of_unit_linear {p : ℕ} [hp : Fact p.Prime] (c : ℤ_[p]) (hc : IsUnit c)
    (tail : ℤ_[p] → ℤ_[p]) (hLip : ∀ s s', ‖tail s - tail s'‖ ≤ ‖s - s'‖)
    {s s' : ℤ_[p]} (hs : c * s + p * tail s = 0) (hs' : c * s' + p * tail s' = 0) : s = s' := by
  have hc1 : ‖c‖ = 1 := PadicInt.isUnit_iff.mp hc
  have heq : c * (s - s') = -((p : ℤ_[p]) * (tail s - tail s')) := by
    linear_combination hs - hs'
  have hnorm : ‖s - s'‖ = (p : ℝ)⁻¹ * ‖tail s - tail s'‖ := by
    have := congrArg norm heq
    rwa [norm_mul, hc1, one_mul, norm_neg, norm_mul, PadicInt.norm_p] at this
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hle : ‖s - s'‖ ≤ (p : ℝ)⁻¹ * ‖s - s'‖ := by
    calc ‖s - s'‖ = (p : ℝ)⁻¹ * ‖tail s - tail s'‖ := hnorm
      _ ≤ (p : ℝ)⁻¹ * ‖s - s'‖ := mul_le_mul_of_nonneg_left (hLip s s') (by positivity)
  have h0 : ‖s - s'‖ = 0 := by
    have hn := norm_nonneg (s - s')
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-! ## 6. The analytic input: Coleman disk certificates -/

/-- **Analytic hypothesis (Chabauty–Coleman on one residue disk at `p = 17`).**

For the residue disk of `C₅(ℚ_17)` above `center ∈ C₅(𝔽₁₇)`, `param` is the rescaled local
uniformizer (`t = 17·s` at `∞` with `t = x²/w`; `w = 17·s` at `(0,0)`), injective on rational points
of the disk. `c·s + 17·tail(s)` is the Coleman integral `∫ ω_ann` from the known point, divided by a
power of 17, with `c` its leading coefficient. The fields are:
* `vanishes`: the integral vanishes at every rational point of the disk. This holds when
  `rank J(ℚ) ≤ 1` and `ω_ann` annihilates `log D`.
* `tail_lipschitz`: the tail is a power series with `ℤ_[17]` coefficients.
* `c_isUnit`: the numerically computed fact `c ≢ 0 (mod 17)` (`c ≡ 3` at `∞`, `c ≡ 15` at `(0,0)`).

Nothing here is proved in Lean. It is the explicit analytic input of the main theorem. -/
structure ColemanDiskCertificate (center : Option (ZMod 17 × ZMod 17)) where
  /-- Rescaled uniformizer on the residue disk. -/
  param : Option (ℚ × ℚ) → ℤ_[17]
  /-- Leading (linear) coefficient of the rescaled Coleman integral. -/
  c : ℤ_[17]
  /-- Higher-order tail of the rescaled Coleman integral. -/
  tail : ℤ_[17] → ℤ_[17]
  c_isUnit : IsUnit c
  tail_lipschitz : ∀ s s', ‖tail s - tail s'‖ ≤ ‖s - s'‖
  param_injective : ∀ P Q : Option (ℚ × ℚ), OnC5 P → OnC5 Q →
    redPt17 P = center → redPt17 Q = center → param P = param Q → P = Q
  vanishes : ∀ P : Option (ℚ × ℚ), OnC5 P → redPt17 P = center →
    c * param P + 17 * tail (param P) = 0

/-- A Coleman disk certificate leaves at most one rational point in its residue disk. -/
theorem ColemanDiskCertificate.eq_of_reduction_eq {center : Option (ZMod 17 × ZMod 17)}
    (K : ColemanDiskCertificate center) {P Q : Option (ℚ × ℚ)} (hP : OnC5 P) (hQ : OnC5 Q)
    (hPc : redPt17 P = center) (hQc : redPt17 Q = center) : P = Q := by
  apply K.param_injective P Q hP hQ hPc hQc
  have h17 : ((17 : ℕ) : ℤ_[17]) = 17 := by norm_num
  exact padic_unique_zero_of_unit_linear (p := 17) K.c K.c_isUnit K.tail K.tail_lipschitz
    (by rw [h17]; exact K.vanishes P hP hPc) (by rw [h17]; exact K.vanishes Q hQ hQc)

/-! ## 7. The Jacobian input and the single-prime Mordell–Weil sieve at `p = 17` -/

/-- Affine Weierstrass points of `C₅` over `𝔽₁₇`. -/
def wpt (a : ZMod 17) : Option (ZMod 17 × ZMod 17) := some (a, 0)

/-- **Jacobian hypotheses** for `C₅`, all explicit:

* `J` stands for `J(ℚ)`, `H` for `J(𝔽₁₇)`, `aj P = [P − ∞]`, `ajp Q = [Q − ∞]` over `𝔽₁₇`,
  `red` the reduction homomorphism, and `D` the class of the Mumford divisor of `mumfordD_relation`.
* `mw_gen`: **rank ≤ 1 with torsion ⊆ ⟨T⟩**, `T = [(0,0) − ∞]`. This is the descent input, not
  checked here.
* `D_mul`, `m_coprime`: `D = m·G (+T)` with `gcd(m, 10) = 1` (2- and 5-saturation, numerically
  certified outside Lean).
* `card_H`: the standard formula `#J(𝔽_q) = (N₁² + N₂)/2 − q` (Weil), applied to the
  Lean-checked counts `countF 17 = 22` and `countF2 17 3 = 350`.
* `ajp_infty`, `ajp_inv`, `ajp_div_y`, `ajp_rigid`: standard divisor facts on the genus-2 curve
  `C₅/𝔽₁₇` (good reduction at 17): `[∞ − ∞] = 0`; `div(x − x_Q) = Q + ιQ − 2∞`;
  `div(y) = Σ W − 5∞`; two effective degree-2 divisors are equivalent only if equal or both
  canonical.
* `aj_red`, `red_D`: reduction is compatible with Abel–Jacobi, and the Mumford representation of
  `D` reduces as in `mumfordD_mod17`. -/
structure C5Rank1JacobianInput where
  /-- Stands for `J(ℚ)`. -/
  J : Type
  [instJ : AddCommGroup J]
  /-- Stands for `J(𝔽₁₇)`. -/
  H : Type
  [instH : AddCommGroup H]
  [finH : Finite H]
  aj : Option (ℚ × ℚ) → J
  red : J →+ H
  ajp : Option (ZMod 17 × ZMod 17) → H
  G : J
  D : J
  m : ℤ
  mw_gen : ∀ x : J, ∃ n : ℤ, x = n • G ∨ x = n • G + aj (some (0, 0))
  D_mul : D = m • G ∨ D = m • G + aj (some (0, 0))
  m_coprime : IsCoprime m 10
  card_H : Nat.card H = (countF 17 ^ 2 + countF2 17 3) / 2 - 17
  aj_red : ∀ P : Option (ℚ × ℚ), OnC5 P → red (aj P) = ajp (redPt17 P)
  red_D : red D = ajp (wpt 12) + ajp (wpt 14)
  ajp_infty : ajp none = 0
  ajp_inv : ∀ Q : Option (ZMod 17 × ZMod 17), OnC5 Q → ajp (hypInv Q) = -ajp Q
  ajp_div_y : ajp (wpt 0) + ajp (wpt 10) + ajp (wpt 11) + ajp (wpt 12) + ajp (wpt 14) = 0
  ajp_rigid : ∀ A B C E : Option (ZMod 17 × ZMod 17), OnC5 A → OnC5 B → OnC5 C → OnC5 E →
    ajp A + ajp B = ajp C + ajp E →
      (A = C ∧ B = E) ∨ (A = E ∧ B = C) ∨ (B = hypInv A ∧ E = hypInv C)

attribute [instance] C5Rank1JacobianInput.instJ C5Rank1JacobianInput.instH
  C5Rank1JacobianInput.finH

theorem wpt_onC5 (a : ZMod 17) (ha : a = 0 ∨ a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 14) :
    OnC5 (wpt a) := by
  show (0 : ZMod 17) ^ 2 = c5 a
  rw [(c5F17_weierstrass a).mpr ha]; ring

theorem eq_none_of_hypInv_eq_none {Q : Option (ZMod 17 × ZMod 17)} (h : none = hypInv Q) :
    Q = none := by
  cases Q with
  | none => rfl
  | some q => simp [hypInv] at h

theorem hypInv_wpt (a : ZMod 17) : hypInv (wpt a) = wpt a := by
  simp [hypInv, wpt]

namespace C5Rank1JacobianInput

theorem two_nsmul_ajp_wpt (I : C5Rank1JacobianInput) (a : ZMod 17) (ha : a = 0 ∨ a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 14) :
    (2 : ℤ) • I.ajp (wpt a) = 0 := by
  have h := I.ajp_inv (wpt a) (wpt_onC5 a ha)
  rw [hypInv_wpt] at h
  rw [two_zsmul]
  nth_rewrite 1 [h]
  exact neg_add_cancel _

/-- Multiplication by `m` is injective on `J(𝔽₁₇)`, since `#J(𝔽₁₇) = 400` and `gcd(m, 10) = 1`. -/
theorem m_smul_injective (I : C5Rank1JacobianInput) {h h' : I.H} (hh : I.m • h = I.m • h') : h = h' := by
  have hcard : Nat.card I.H = 400 := by rw [I.card_H]; decide +kernel
  have h400 : IsCoprime I.m 400 :=
    (I.m_coprime.pow_right (n := 4)).of_isCoprime_of_dvd_right (by norm_num)
  obtain ⟨u, v, huv⟩ := h400
  have hkill : ∀ z : I.H, (400 : ℤ) • z = 0 := by
    intro z
    have := card_nsmul_eq_zero' (x := z)
    rw [hcard] at this
    exact_mod_cast this
  have key : ∀ z : I.H, z = u • (I.m • z) := by
    intro z
    calc z = ((u * I.m + v * 400 : ℤ)) • z := by rw [huv, one_zsmul]
      _ = u • (I.m • z) + v • ((400 : ℤ) • z) := by rw [add_zsmul, mul_zsmul, mul_zsmul]
      _ = u • (I.m • z) := by rw [hkill, zsmul_zero, add_zero]
  rw [key h, key h', hh]

/-- Every rational point reduces mod 17 to `∞` or `(0, 0)` (single-prime Mordell–Weil sieve). -/
theorem reduction_mem_known (I : C5Rank1JacobianInput) {P : Option (ℚ × ℚ)} (hP : OnC5 P) :
    redPt17 P = none ∨ redPt17 P = wpt 0 := by
  -- 2-torsion bookkeeping in `H = J(𝔽₁₇)`
  set w : ZMod 17 → I.H := fun a => I.ajp (wpt a) with hw
  have w0 := I.two_nsmul_ajp_wpt 0 (by decide)
  have w10 := I.two_nsmul_ajp_wpt 10 (by decide)
  have w11 := I.two_nsmul_ajp_wpt 11 (by decide)
  have w12 := I.two_nsmul_ajp_wpt 12 (by decide)
  have w14 := I.two_nsmul_ajp_wpt 14 (by decide)
  have hT : I.red (I.aj (some (0, 0))) = I.ajp (wpt 0) := by
    rw [I.aj_red _ onC5_known.2, redPt17_zero]; rfl
  set T' := I.ajp (wpt 0)
  set D17 := I.ajp (wpt 12) + I.ajp (wpt 14)
  have hD17 : (2 : ℤ) • D17 = 0 := by rw [zsmul_add, w12, w14, add_zero]
  -- `red G` equals a 2-torsion element `D' ∈ {D17, D17 + T'}`
  have hodd : Odd I.m := by
    have h2 : IsCoprime I.m 2 := I.m_coprime.of_isCoprime_of_dvd_right (by norm_num)
    rcases Int.even_or_odd I.m with ⟨k, hk⟩ | ho
    · exfalso
      have : (2 : ℤ) ∣ I.m := ⟨k, by omega⟩
      exact absurd (h2.isUnit_of_dvd' this (dvd_refl 2)) (by decide)
    · exact ho
  obtain ⟨k, hk⟩ := hodd
  have hfix : ∀ z : I.H, (2 : ℤ) • z = 0 → I.m • z = z := by
    intro z hz
    rw [hk, add_zsmul, mul_comm, mul_zsmul, hz, zsmul_zero, zero_add, one_zsmul]
  have hG : ∃ D' : I.H, (2 : ℤ) • D' = 0 ∧ (D' = D17 ∨ D' = D17 + T') ∧ I.red I.G = D' := by
    rcases I.D_mul with hDm | hDm
    · refine ⟨D17, hD17, Or.inl rfl, I.m_smul_injective ?_⟩
      rw [hfix _ hD17, ← map_zsmul, ← hDm, I.red_D]
    · have h2 : (2 : ℤ) • (D17 + T') = 0 := by rw [zsmul_add, hD17, w0, add_zero]
      refine ⟨D17 + T', h2, Or.inr rfl, I.m_smul_injective ?_⟩
      rw [hfix _ h2]
      have : I.red I.D = I.m • I.red I.G + T' := by rw [hDm, map_add, map_zsmul, hT]
      rw [I.red_D] at this
      calc I.m • I.red I.G = (I.m • I.red I.G + T') + T' := by
            rw [add_assoc, ← two_zsmul, w0, add_zero]
        _ = D17 + T' := by rw [← this]
  obtain ⟨D', hD'2, hD'cases, hGD'⟩ := hG
  have hnD : ∀ n : ℤ, n • D' = 0 ∨ n • D' = D' := by
    intro n
    rcases Int.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · left; rw [hj, ← two_mul, mul_comm, mul_zsmul, hD'2, zsmul_zero]
    · right; rw [hj, add_zsmul, mul_comm, mul_zsmul, hD'2, zsmul_zero, zero_add, one_zsmul]
  -- the reduction of `[P − ∞]` lies in `{0, T', D17, D17 + T'}`
  set Q := redPt17 P with hQ
  have hQon : OnC5 Q := redPt17_onC5 hP
  have himg : I.ajp Q = 0 ∨ I.ajp Q = T' ∨ I.ajp Q = D17 ∨ I.ajp Q = D17 + T' := by
    rw [hQ, ← I.aj_red P hP]
    obtain ⟨n, hn | hn⟩ := I.mw_gen (I.aj P)
    · rw [hn, map_zsmul, hGD']
      rcases hnD n with h | h <;> rw [h]
      · exact Or.inl rfl
      · rcases hD'cases with h' | h' <;> rw [h'] <;> simp
    · rw [hn, map_add, map_zsmul, hGD', hT]
      rcases hnD n with h | h <;> rw [h]
      · simp
      · rcases hD'cases with h' | h' <;> rw [h']
        · simp
        · right; right; left
          rw [add_assoc, ← two_zsmul, w0, add_zero]
  have honInf : OnC5 (none : Option (ZMod 17 × ZMod 17)) := trivial
  have hon : ∀ a : ZMod 17, (a = 0 ∨ a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 14) → OnC5 (wpt a) :=
    wpt_onC5
  -- `D17 + T' = [W₁₀ + W₁₁ − 2∞]`, from `div(y)`
  have hDT : D17 + T' = I.ajp (wpt 10) + I.ajp (wpt 11) := by
    have hy := I.ajp_div_y
    have e10 : -I.ajp (wpt 10) = I.ajp (wpt 10) := by
      rw [neg_eq_iff_add_eq_zero, ← two_zsmul, w10]
    have e11 : -I.ajp (wpt 11) = I.ajp (wpt 11) := by
      rw [neg_eq_iff_add_eq_zero, ← two_zsmul, w11]
    have : D17 + T' = -(I.ajp (wpt 10) + I.ajp (wpt 11)) := by
      simp only [D17, T']
      rw [eq_neg_iff_add_eq_zero, ← hy]; abel
    rw [this, neg_add, e10, e11]
  rcases himg with h | h | h | h
  · -- `[Q − ∞] = 0` forces `Q = ∞`
    have := I.ajp_rigid Q none none none hQon honInf honInf honInf
      (by simp [h, I.ajp_infty])
    left
    rcases this with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact h1
    · exact eq_none_of_hypInv_eq_none h1
  · -- `[Q − ∞] = T'` forces `Q = (0, 0)`
    have := I.ajp_rigid Q none (wpt 0) none hQon honInf (hon 0 (by decide)) honInf
      (by rw [h, I.ajp_infty, add_zero])
    right
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h1
    · simp [wpt] at h2
    · simp [hypInv, wpt] at h2
  · -- `[Q − ∞] = D17` is impossible
    exfalso
    have := I.ajp_rigid Q none (wpt 12) (wpt 14) hQon honInf (hon 12 (by decide))
      (hon 14 (by decide)) (by rw [h, I.ajp_infty, add_zero])
    rcases this with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · simp [wpt] at h2
    · simp [wpt] at h2
    · rw [hypInv_wpt] at h2; simp [wpt] at h2; exact absurd h2 (by decide)
  · -- `[Q − ∞] = D17 + T' = [W₁₀ + W₁₁ − 2∞]` is impossible
    exfalso
    have := I.ajp_rigid Q none (wpt 10) (wpt 11) hQon honInf (hon 10 (by decide))
      (hon 11 (by decide)) (by rw [h, I.ajp_infty, add_zero, hDT])
    rcases this with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · simp [wpt] at h2
    · simp [wpt] at h2
    · rw [hypInv_wpt] at h2; simp [wpt] at h2; exact absurd h2 (by decide)

end C5Rank1JacobianInput

/-- **Main theorem (conditional).** Under the explicit Jacobian hypotheses `I`
(rank `J(ℚ) ≤ 1`, saturation, standard divisor facts over `𝔽₁₇`) and Coleman disk certificates
`K∞`, `K₀` at `p = 17`, the rational points of `C₅ : w² = x⁵ + 89x⁴ + 2796x³ + 35704x² + 123200x`
are exactly `∞` and `(0, 0)`. -/
theorem c5_rational_points_of_rank_one (I : C5Rank1JacobianInput)
    (Kinf : ColemanDiskCertificate none) (K0 : ColemanDiskCertificate (wpt 0))
    (P : Option (ℚ × ℚ)) : OnC5 P ↔ P = none ∨ P = some (0, 0) := by
  constructor
  · intro hP
    rcases I.reduction_mem_known hP with h | h
    · left
      exact Kinf.eq_of_reduction_eq hP onC5_known.1 h rfl
    · right
      exact K0.eq_of_reduction_eq hP onC5_known.2 h redPt17_zero
  · rintro (rfl | rfl)
    · exact onC5_known.1
    · exact onC5_known.2

#print axioms c5_intCast
#print axioms mumfordD_relation
#print axioms mumfordD_a_no_rational_root
#print axioms c5F17_card_points
#print axioms c5F17_weierstrass
#print axioms mumfordD_mod17
#print axioms c5_countF_17
#print axioms c5_count_F289
#print axioms c5_jacobian_count_F17
#print axioms c5_jacobian_counts_13_29_41
#print axioms redPt17_onC5
#print axioms redPt17_zero
#print axioms padic_unique_zero_of_unit_linear
#print axioms ColemanDiskCertificate.eq_of_reduction_eq
#print axioms C5Rank1JacobianInput.m_smul_injective
#print axioms C5Rank1JacobianInput.reduction_mem_known
#print axioms c5_rational_points_of_rank_one

end Research.Erdos885C5Chabauty
