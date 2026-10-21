import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
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

theorem exclude_first_1 (p : ℝ) (b : ℤ) (hp : 0 ≤ p) (hb : 0 ≤ b)
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
