import Mathlib.Tactic
namespace M09Critic
variable {A : Type*} [Ring A]

/-- Fixed-K congruence induces similarity only when the same K is preserved. -/
theorem relative_intertwining (K S Si Sd T U : A)
    (hK : K*K=1) (hleft : Si*S=1) (hright : S*Si=1)
    (hmetric : Sd*K*S=K) (hform : Sd*K*T*S=K*U) : T*S=S*U := by
  have hrow : Sd*K=K*Si := by
    calc
      Sd*K = Sd*K*(S*Si) := by rw [hright, mul_one]
      _ = (Sd*K*S)*Si := by simp only [mul_assoc]
      _ = K*Si := by rw [hmetric]
  have hform' : (K*Si)*T*S=K*U := by rw [hrow] at hform; exact hform
  have he := congrArg (fun X : A => S*K*X) hform'
  simpa only [mul_assoc, ← mul_assoc K K, hK, one_mul,
    ← mul_assoc S Si, hright] using he

/-- Conjugating every represented operator preserves its multiplication table. -/
theorem conjugated_product (S Si X Y : A) (h : S*Si=1) :
    (Si*X*S)*(Si*Y*S)=Si*(X*Y)*S := by
  calc
    _ = Si*X*(S*Si)*Y*S := by noncomm_ring
    _ = Si*(X*Y)*S := by rw [h]; noncomm_ring

/-- The derivative term is required even when the old connection is zero. -/
theorem moving_frame_cancellation (S Si Sp psi : A) (h : S*Si=1) :
    -(Si*Sp*Si*psi)+(Si*Sp)*(Si*psi)=0 := by noncomm_ring
end M09Critic
#print axioms M09Critic.relative_intertwining
#print axioms M09Critic.conjugated_product
#print axioms M09Critic.moving_frame_cancellation
