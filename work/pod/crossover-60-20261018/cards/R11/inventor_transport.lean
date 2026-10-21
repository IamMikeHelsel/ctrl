import Mathlib.Tactic

/- Algebraic transport identities. Instantiation as derivatives of rotation paths
   requires the explicitly documented product-rule and frame hypotheses. -/
namespace CrossoverR11Inventor

theorem transport_first {A : Type*} [Ring A] (W P C : A) :
    (C-W*P)+W*P=C := by noncomm_ring

theorem transport_second {A : Type*} [Ring A] (W W1 P C E : A) :
    (E-2*W*C+(W*W-W1)*P) + 2*W*(C-W*P)+(W1+W*W)*P = E := by
  noncomm_ring

theorem transport_third {A : Type*} [Ring A] (W W1 W2 P C E F : A) :
    (F-3*W*E+3*(W*W-W1)*C+(2*W1*W+W*W1-W2-W*W*W)*P) +
      3*W*(E-2*W*C+(W*W-W1)*P) +
      3*(W1+W*W)*(C-W*P) +
      (W2+2*W*W1+W1*W+W*W*W)*P = F := by
  noncomm_ring

theorem constant_frame_transport {A : Type*} [Ring A] (R Q Qi P : A)
    (hinv : Q*Qi=1) : (R*Q)*(Qi*P)=R*P := by
  calc
    (R*Q)*(Qi*P) = R*((Q*Qi)*P) := by noncomm_ring
    _ = R*P := by rw [hinv]; simp

theorem opposed_rate_exceeds_cap :
    |(-1:ℝ)-1| > (3/2:ℝ) ∧ |(1:ℝ)-1|=0 := by norm_num

#print axioms transport_first
#print axioms transport_second
#print axioms transport_third
#print axioms constant_frame_transport
#print axioms opposed_rate_exceeds_cap
end CrossoverR11Inventor
