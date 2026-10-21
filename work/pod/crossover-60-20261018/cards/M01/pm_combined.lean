import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/- AI-written generic adjacent-factor exclusion. It checks factor-gap certificates,
   not the execution or full coverage of the original bounded search. -/
set_option autoImplicit false
namespace M01Gap

theorem adjacent_factor_gap (p target : ℝ) (k b : ℤ)
    (hp : 0 ≤ p) (hk : 0 ≤ k) (hb : 0 ≤ b)
    (lower : (k:ℝ)*((k:ℝ)+p) < target)
    (upper : target < ((k:ℝ)+1)*((k:ℝ)+1+p))
    (root : (b:ℝ)*((b:ℝ)+p) = target) : False := by
  have hkr : (0:ℝ) ≤ k := by exact_mod_cast hk
  have hbr : (0:ℝ) ≤ b := by exact_mod_cast hb
  by_cases h : b ≤ k
  · have hbk : (b:ℝ) ≤ k := by exact_mod_cast h
    have nonneg : 0 ≤ ((k:ℝ)-b)*((k:ℝ)+b+p) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have hi : k+1 ≤ b := by omega
    have hkb : (k:ℝ)+1 ≤ b := by exact_mod_cast hi
    have nonneg : 0 ≤ ((b:ℝ)-(k+1))*((b:ℝ)+(k+1)+p) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

#print axioms adjacent_factor_gap

theorem exclude_first_1 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*1*(1+p)) : False := by
  apply adjacent_factor_gap p ((677376000/206222625:ℝ)*1*(1+p)) 3 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_first_1

theorem exclude_first_2 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*2*(2+p)) : False := by
  apply adjacent_factor_gap p ((677376000/206222625:ℝ)*2*(2+p)) 6 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_first_2

theorem exclude_first_3 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*3*(3+p)) : False := by
  apply adjacent_factor_gap p ((677376000/206222625:ℝ)*3*(3+p)) 9 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_first_3

theorem exclude_first_4 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*4*(4+p)) : False := by
  apply adjacent_factor_gap p ((677376000/206222625:ℝ)*4*(4+p)) 13 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_first_4

theorem exclude_first_5 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*5*(5+p)) : False := by
  apply adjacent_factor_gap p ((677376000/206222625:ℝ)*5*(5+p)) 16 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_first_5

theorem exclude_first_6 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*6*(6+p)) : False := by
  apply adjacent_factor_gap p ((677376000/206222625:ℝ)*6*(6+p)) 19 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_first_6

theorem exclude_first_7 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*7*(7+p)) : False := by
  apply adjacent_factor_gap p ((677376000/206222625:ℝ)*7*(7+p)) 22 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_first_7

theorem exclude_first_8 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*8*(8+p)) : False := by
  apply adjacent_factor_gap p ((677376000/206222625:ℝ)*8*(8+p)) 26 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_first_8

theorem exclude_first_9 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*9*(9+p)) : False := by
  apply adjacent_factor_gap p ((677376000/206222625:ℝ)*9*(9+p)) 29 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_first_9

theorem exclude_first_10 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*10*(10+p)) : False := by
  apply adjacent_factor_gap p ((677376000/206222625:ℝ)*10*(10+p)) 32 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_first_10

theorem exclude_first_11 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*11*(11+p)) : False := by
  apply adjacent_factor_gap p ((677376000/206222625:ℝ)*11*(11+p)) 36 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_first_11

theorem exclude_second_1 (p : ℝ) (b : ℤ) (hp : 18446744073708551616 ≤ p) (hb : 0 ≤ b)
    (root : (b:ℝ)*((b:ℝ)+p) = (115706752/24561225:ℝ)*1*(1+p)) : False := by
  apply adjacent_factor_gap p ((115706752/24561225:ℝ)*1*(1+p)) 4 b (by linarith) (by norm_num) hb
  · nlinarith
  · nlinarith
  · exact root
#print axioms exclude_second_1

end M01Gap
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
namespace M01Combined
theorem first_valid_bound (p q : ℝ) (a b : ℤ)
    (hq : 0 ≤ q) (hqm : q ≤ 1000000) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (ra : (a:ℝ)*((a:ℝ)+p)=206222625*q*q)
    (rb : (b:ℝ)*((b:ℝ)+p)=677376000*q*q) : p ≤ 18446744073708551616 := by
  by_contra h
  have hp : 18446744073708551616 ≤ p := by linarith
  have cap := M01Bounds.first_factor_cap p q a hp hq hqm ha ra
  have eq : (b:ℝ)*((b:ℝ)+p) = (677376000/206222625:ℝ)*(a:ℝ)*((a:ℝ)+p) := by
    calc
      _ = 677376000*q*q := rb
      _ = (677376000/206222625:ℝ)*((a:ℝ)*((a:ℝ)+p)) := by rw [ra]; ring
      _ = _ := by ring
  have cases : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 := by omega
  rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · subst a
    exact M01Gap.exclude_first_1 p b hp hb (by simpa using eq)
  · subst a
    exact M01Gap.exclude_first_2 p b hp hb (by simpa using eq)
  · subst a
    exact M01Gap.exclude_first_3 p b hp hb (by simpa using eq)
  · subst a
    exact M01Gap.exclude_first_4 p b hp hb (by simpa using eq)
  · subst a
    exact M01Gap.exclude_first_5 p b hp hb (by simpa using eq)
  · subst a
    exact M01Gap.exclude_first_6 p b hp hb (by simpa using eq)
  · subst a
    exact M01Gap.exclude_first_7 p b hp hb (by simpa using eq)
  · subst a
    exact M01Gap.exclude_first_8 p b hp hb (by simpa using eq)
  · subst a
    exact M01Gap.exclude_first_9 p b hp hb (by simpa using eq)
  · subst a
    exact M01Gap.exclude_first_10 p b hp hb (by simpa using eq)
  · subst a
    exact M01Gap.exclude_first_11 p b hp hb (by simpa using eq)
#print axioms first_valid_bound
theorem second_valid_bound (p q : ℝ) (a b : ℤ)
    (hq : 0 ≤ q) (hqm : q ≤ 1000000) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (ra : (a:ℝ)*((a:ℝ)+p)=24561225*q*q)
    (rb : (b:ℝ)*((b:ℝ)+p)=115706752*q*q) : p ≤ 18446744073708551616 := by
  by_contra h
  have hp : 18446744073708551616 ≤ p := by linarith
  have cap := M01Bounds.second_factor_cap p q a hp hq hqm ha ra
  have eq : (b:ℝ)*((b:ℝ)+p) = (115706752/24561225:ℝ)*(a:ℝ)*((a:ℝ)+p) := by
    calc
      _ = 115706752*q*q := rb
      _ = (115706752/24561225:ℝ)*((a:ℝ)*((a:ℝ)+p)) := by rw [ra]; ring
      _ = _ := by ring
  have ae : a = 1 := by omega
  subst a
  exact M01Gap.exclude_second_1 p b hp hb (by simpa using eq)
#print axioms second_valid_bound
end M01Combined
