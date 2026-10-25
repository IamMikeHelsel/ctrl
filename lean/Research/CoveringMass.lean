import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Finite arithmetic supporting a proposed 7-smooth covering exclusion

AI-assisted, 2026-10-18. This certifies the finite sieve and numerical bounds.
Connecting these computations to arbitrary finite covering systems is separate.
-/

namespace Research.CoveringMass

def sieveDivisors : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
    67, 71, 73, 79, 83, 89, 97]

def passesSieve (m : ℕ) : Bool :=
  decide (4 ≤ m) && sieveDivisors.all (fun q => decide ((m + 1) % q ≠ 0 ∨ m + 1 = q))

theorem prime_passes_sieve (m : ℕ) (hm : 4 ≤ m) (hp : (m + 1).Prime) :
    passesSieve m = true := by
  simp only [passesSieve, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hm, List.all_eq_true.mpr ?_⟩
  intro q hq
  simp only [decide_eq_true_eq]
  have hq' : 1 < q := by
    have : ∀ q ∈ sieveDivisors, 1 < q := by decide
    exact this q hq
  by_cases h : (m + 1) % q = 0
  · right
    exact ((hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero h)).resolve_left
      (by omega)).symm
  · exact Or.inl h

def exponentBox : List ℕ :=
  (List.range 10).flatMap fun a =>
    (List.range 7).flatMap fun b =>
      (List.range 5).flatMap fun c =>
        (List.range 4).map fun d => 2 ^ (a + 1) * 3 ^ b * 5 ^ c * 7 ^ d

def denominator : ℕ := 2^10 * 3^6 * 5^4 * 7^3

def remainderBox : List ℕ :=
  exponentBox.filter fun m => passesSieve m && decide (m ∉ ([4, 6, 10, 12] : List ℕ))

def groupNumerator (g : ℕ) : ℕ :=
  ((remainderBox.filter fun m => m.gcd 60 == g).map fun m => denominator / m).sum

/-- Each retained modulus divides the common denominator, so division in the
mass calculation is exact rather than silently rounded down. -/
theorem grid_division_exact :
    ∀ m ∈ exponentBox, 0 < m ∧ denominator % m = 0 := by
  set_option maxRecDepth 4096 in decide +kernel

/-- Every possible gcd group is represented in the numerical certificate. -/
theorem gcd_groups_complete :
    ∀ m ∈ remainderBox, m.gcd 60 ∈ ([4, 6, 10, 12, 20, 30, 60] : List ℕ) := by
  set_option maxRecDepth 4096 in decide +kernel

/-- All seven finite mass upper bounds, with common denominator 1000. -/
theorem grid_mass_bounds :
    1000 * groupNumerator 4 ≤ 120 * denominator ∧
    1000 * groupNumerator 6 ≤ 101 * denominator ∧
    1000 * groupNumerator 10 ≤ 21 * denominator ∧
    1000 * groupNumerator 12 ≤ 85 * denominator ∧
    1000 * groupNumerator 20 ≤ 47 * denominator ∧
    1000 * groupNumerator 30 ≤ 56 * denominator ∧
    1000 * groupNumerator 60 ≤ 40 * denominator := by
  set_option maxRecDepth 4096 in decide +kernel

#print axioms prime_passes_sieve
#print axioms grid_division_exact
#print axioms gcd_groups_complete
#print axioms grid_mass_bounds

end Research.CoveringMass
