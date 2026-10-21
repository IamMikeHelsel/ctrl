import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace M01FactorGap

/-- Polynomial identity required by any common factor difference. -/
theorem factor_gap_identity (A B a c p q : ℚ)
    (ha : a*(a+p)=A*q^2) (hc : c*(c+p)=B*q^2) :
    q^2*(B*a-A*c)=a*c*(c-a) := by
  have h1 := congrArg (fun t : ℚ => a*t) hc
  have h2 := congrArg (fun t : ℚ => c*t) ha
  nlinarith [h1,h2]

/-- Conditional integer-bracket gate. The caller establishes c<=L using the
 strict rational bound c<B*a/A and integrality of c, then L=ceil(B*a/A)-1.
 This theorem does not hide that integer-floor bridge in a changed statement. -/
theorem gap_necessary (A B a c p q L : ℚ)
    (hA : 0 ≤ A) (ha0 : 0 ≤ a) (hac : a ≤ c) (hcL : c ≤ L)
    (ha : a*(a+p)=A*q^2) (hc : c*(c+p)=B*q^2) :
    q^2*(B*a-A*L) ≤ a*L*(L-a) := by
  have hi := factor_gap_identity A B a c p q ha hc
  have hsum : 0 ≤ L+c-a := by linarith
  have hfac : 0 ≤ a*(L+c-a)+A*q^2 :=
    add_nonneg (mul_nonneg ha0 hsum) (mul_nonneg hA (sq_nonneg q))
  have hm : 0 ≤ (L-c)*(a*(L+c-a)+A*q^2) :=
    mul_nonneg (sub_nonneg.mpr hcL) hfac
  nlinarith [hm]

theorem gap_excludes (A B a c p q L : ℚ)
    (hA : 0 ≤ A) (ha0 : 0 ≤ a) (hac : a ≤ c) (hcL : c ≤ L)
    (ha : a*(a+p)=A*q^2)
    (hgap : a*L*(L-a) < q^2*(B*a-A*L)) :
    c*(c+p) ≠ B*q^2 := by
  intro hc
  exact (not_lt_of_ge (gap_necessary A B a c p q L hA ha0 hac hcL ha hc)) hgap

#print axioms factor_gap_identity
#print axioms gap_necessary
#print axioms gap_excludes
end M01FactorGap
