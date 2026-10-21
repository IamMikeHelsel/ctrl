import Mathlib.Tactic
namespace M09Similarity
variable {A : Type*} [Ring A] [Algebra ℂ A] [Nontrivial A]

-- Conditional algebra bridge: K-unitary simultaneous form congruence induces
-- this intertwining of the relative operators. That implication is separate.
theorem squared_parameter (W S : A) (s t : ℝ)
    (hW : W*W= -1) (hS : S≠0)
    (hinter : S*((t:ℂ) • W)=((s:ℂ) • W)*S) : t^2=s^2 := by
  have ht : ((t:ℂ) • W)*((t:ℂ) • W)=(-(t:ℂ)^2) • (1:A) := by
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul,hW,smul_neg,neg_smul]
    congr 1; ring
  have hs : ((s:ℂ) • W)*((s:ℂ) • W)=(-(s:ℂ)^2) • (1:A) := by
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul,hW,smul_neg,neg_smul]
    congr 1; ring
  have he : S*(((t:ℂ) • W)*((t:ℂ) • W)) =
      (((s:ℂ) • W)*((s:ℂ) • W))*S := by
    calc
      _ = (S*((t:ℂ) • W))*((t:ℂ) • W) := by rw [mul_assoc]
      _ = (((s:ℂ) • W)*S)*((t:ℂ) • W) := by rw [hinter]
      _ = (((s:ℂ) • W)*((s:ℂ) • W))*S := by rw [mul_assoc,hinter,← mul_assoc]
  rw [ht,hs,mul_smul_comm,smul_mul_assoc,mul_one,one_mul] at he
  have hc : (-(t:ℂ)^2)=(-(s:ℂ)^2) := (smul_left_injective ℂ hS) he
  have hc' : (t:ℂ)^2=(s:ℂ)^2 := neg_injective hc
  exact_mod_cast hc'
end M09Similarity
#print axioms M09Similarity.squared_parameter
