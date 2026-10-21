import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace C02Certificate

-- AI-written conditional objective certificates, not a plant model or ODE enclosure.
theorem two_active_lower_bound (a b d e c J : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (first : d + a*c ≤ J) (second : e - b*c ≤ J) :
    b*d+a*e ≤ (a+b)*J := by
  have h1 := mul_le_mul_of_nonneg_left first hb
  have h2 := mul_le_mul_of_nonneg_left second ha
  nlinarith

theorem affine_tube_convex {I : Type} (a b : I → ℝ) (c1 c2 J1 J2 theta : ℝ)
    (ht : 0 ≤ theta) (ht1 : theta ≤ 1)
    (h1 : ∀ i, |b i+c1*a i| ≤ J1) (h2 : ∀ i, |b i+c2*a i| ≤ J2) :
    ∀ i, |b i+(theta*c1+(1-theta)*c2)*a i| ≤ theta*J1+(1-theta)*J2 := by
  intro i
  have hm : 0 ≤ 1-theta := by linarith
  calc
    |b i+(theta*c1+(1-theta)*c2)*a i|
        = |theta*(b i+c1*a i)+(1-theta)*(b i+c2*a i)| := by congr 1; ring
    _ ≤ |theta*(b i+c1*a i)|+|(1-theta)*(b i+c2*a i)| := abs_add_le _ _
    _ = theta*|b i+c1*a i|+(1-theta)*|b i+c2*a i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg hm]
    _ ≤ theta*J1+(1-theta)*J2 :=
      add_le_add (mul_le_mul_of_nonneg_left (h1 i) ht)
        (mul_le_mul_of_nonneg_left (h2 i) hm)
#print axioms two_active_lower_bound
#print axioms affine_tube_convex
end C02Certificate
