import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace M01Bounds

-- AI-written bridge: exact arithmetic, not execution coverage of the C++ search.
theorem safe_discriminant (p q n : ℝ) (hp : 0 ≤ p)
    (hpmax : p ≤ 18446744073708551616) (hq : 0 ≤ q)
    (hqmax : q ≤ 1000000) (hn : 0 ≤ n) (hnmax : n ≤ 16670745700) :
    p*p + 4*n*q*q < 340282366920938463463374607431768211456 := by
  have ps : p*p ≤ 18446744073708551616*18446744073708551616 :=
    mul_self_le_mul_self hp hpmax
  have qs : q*q ≤ (1000000000000:ℝ) := by nlinarith
  have nq : n*(q*q) ≤ 16670745700*1000000000000 := by
    calc
      n*(q*q) ≤ n*1000000000000 := mul_le_mul_of_nonneg_left qs hn
      _ ≤ 16670745700*1000000000000 := mul_le_mul_of_nonneg_right hnmax (by norm_num)
  nlinarith

 theorem first_factor_cap (p q : ℝ) (a : ℤ)
    (hp : 18446744073708551616 ≤ p) (hq : 0 ≤ q) (hqm : q ≤ 1000000)
    (ha : 1 ≤ a) (root : (a:ℝ)*((a:ℝ)+p)=206222625*q*q) : a ≤ 11 := by
  by_contra h
  have ai : 12 ≤ a := by omega
  have ar : (12:ℝ) ≤ a := by exact_mod_cast ai
  have qs : q*q ≤ (1000000000000:ℝ) := by nlinarith
  have prod : 0 ≤ ((a:ℝ)-12)*(p-18446744073708551616) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [sq_nonneg (a:ℝ)]

 theorem second_factor_cap (p q : ℝ) (a : ℤ)
    (hp : 18446744073708551616 ≤ p) (hq : 0 ≤ q) (hqm : q ≤ 1000000)
    (ha : 1 ≤ a) (root : (a:ℝ)*((a:ℝ)+p)=24561225*q*q) : a ≤ 1 := by
  by_contra h
  have ai : 2 ≤ a := by omega
  have ar : (2:ℝ) ≤ a := by exact_mod_cast ai
  have qs : q*q ≤ (1000000000000:ℝ) := by nlinarith
  have prod : 0 ≤ ((a:ℝ)-2)*(p-18446744073708551616) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [sq_nonneg (a:ℝ)]
#print axioms safe_discriminant
#print axioms first_factor_cap
#print axioms second_factor_cap
end M01Bounds
