import Mathlib.Tactic
namespace M09Flip
variable {A : Type*} [Ring A] [Algebra ℂ A]
-- Actual-source instantiation: G is the complex matrix of cgamma7,
-- D its conjugate transpose. The hypotheses are source Clifford identities.
theorem unitary (K G D : A) (hG : G*G= -1) (hD : D*K= -(K*G)) :
    D*K*G=K := by rw [hD,neg_mul,mul_assoc,hG,mul_neg,mul_one,neg_neg]

theorem inner_flip (G W : A) (hG : G*G= -1) (hanti : G*W= -(W*G)) :
    G*W*G=W := by rw [hanti,neg_mul,mul_assoc,hG,mul_neg,mul_one,neg_neg]

theorem form_flip (K G D W : A) (t : ℂ)
    (hG : G*G= -1) (hD : D*K= -(K*G)) (hanti : G*W= -(W*G)) :
    D*(K*(1+t • W))*G=K*(1+(-t) • W) := by
  have hu := unitary K G D hG hD
  have hi := inner_flip G W hG hanti
  have hw : D*K*W*G= -(K*W) := by
    rw [hD,neg_mul,neg_mul,mul_assoc,mul_assoc,← mul_assoc G W G,hi]
  simp only [mul_add,mul_one,add_mul,mul_smul_comm,smul_mul_assoc,← mul_assoc]
  rw [hu,hw,smul_neg,neg_smul]
end M09Flip
#print axioms M09Flip.unitary
#print axioms M09Flip.inner_flip
#print axioms M09Flip.form_flip
