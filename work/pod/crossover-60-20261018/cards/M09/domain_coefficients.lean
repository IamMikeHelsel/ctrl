import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
namespace M09Domain

theorem real_congruence_coefficients (t : ℝ) :
    ∃ a b : ℝ, 0<a ∧ a^2-b^2=1 ∧ 2*a*b=t ∧ 0<a^2+b^2 := by
  let q := Real.sqrt (1+t^2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq : q^2=1+t^2 := Real.sq_sqrt (by nlinarith [sq_nonneg t])
  have hq1 : 1 ≤ q := by nlinarith
  let a := Real.sqrt ((q+1)/2)
  have ha : 0<a := Real.sqrt_pos.2 (by linarith)
  have ha2 : a^2=(q+1)/2 := Real.sq_sqrt (by linarith)
  let b := t/(2*a)
  have hab : 2*a*b=t := by dsimp [b]; field_simp
  have hcoef : a^2-b^2=1 := by
    have hb : 4*a^2*b^2=t^2 := by
      calc
        _ = (2*a*b)^2 := by ring
        _ = t^2 := by rw [hab]
    have hmult : 4*a^2*(a^2-b^2-1)=0 := by
      calc
        _ = (2*a^2-1)^2-1-4*a^2*b^2 := by ring
        _ = q^2-1-t^2 := by rw [show 2*a^2-1=q by linarith,hb]
        _ = 0 := by rw [hq]; ring
    have hane : 4*a^2 ≠ 0 := by positivity
    have hz := (mul_eq_zero.mp hmult).resolve_left hane
    linarith
  exact ⟨a,b,ha,hcoef,hab,by nlinarith [sq_nonneg b]⟩

theorem quotient_inverse_coefficients (a b : ℝ) :
    a*a-b*(-b)=a^2+b^2 ∧ a*(-b)+b*a=0 := by constructor <;> ring

theorem fixed_metric_with_same_coefficients (a b t : ℝ)
    (h : 2*a*b=t) (hunitary : 2*a*b=0) : t=0 := by linarith

theorem squared_parameter_iff (s t : ℝ) : s^2=t^2 ↔ s=t ∨ s= -t := by
  constructor
  · intro h
    have hprod : (s-t)*(s+t)=0 := by nlinarith
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> ring
end M09Domain
#print axioms M09Domain.real_congruence_coefficients
#print axioms M09Domain.quotient_inverse_coefficients
#print axioms M09Domain.fixed_metric_with_same_coefficients
#print axioms M09Domain.squared_parameter_iff
