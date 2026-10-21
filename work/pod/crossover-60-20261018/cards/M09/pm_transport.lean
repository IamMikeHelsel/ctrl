import Mathlib
noncomputable section
namespace M09Transport
open Matrix
abbrev M := Matrix (Fin 2) (Fin 2) ℝ
def K : M := !![1, 0; 0, -1]
def W : M := !![0, 1; -1, 0]
def H (t : ℝ) : M := !![1, t; t, -1]
def S : M := !![5/3, 4/3; -4/3, 5/3]
def T : M := !![15/41, -12/41; 12/41, 15/41]
def G : M := !![9/41, 40/41; 40/41, -9/41]
def y : Fin 2 → ℝ := ![15/41, 12/41]
def form (A : M) (v : Fin 2 → ℝ) : ℝ := dotProduct v (A.mulVec v)
theorem congruence : S.transpose * K * S = H (40/9) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [S,K,H, Matrix.mul_apply, Fin.sum_univ_two]
theorem inverse : T * S = 1 ∧ S * T = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [S,T, Matrix.mul_apply, Fin.sum_univ_two]
theorem clifford_transport : T * K * S = G := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [S,T,K,G, Matrix.mul_apply, Fin.sum_univ_two]
theorem transported_square : G * G = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [G, Matrix.mul_apply, Fin.sum_univ_two]
theorem all_fields : form (H (40/9) * G) y = 1 := by
  norm_num [form,H,G,y, dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two]
theorem frozen_generator : form (H (40/9) * K) y = 9/41 := by
  norm_num [form,H,K,y, dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two]
-- This is a decorated-pair invariant, conditional on retaining both forms and W.
theorem pencil_square (t : ℝ) : (K * H t - 1) * (K * H t - 1) = -(t*t) • (1:M) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [K,H,Matrix.mul_apply,Fin.sum_univ_two]
theorem decorated_parameter (t : ℝ) : Matrix.trace (W * (K * H t - 1)) = -2*t := by
  simp [W,K,H,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two]
  ring
theorem trace_transport {n : Type*} [Fintype n] [DecidableEq n]
    (S T W L : Matrix n n ℝ) (h : S*T=1) :
    Matrix.trace ((T*W*S)*(T*L*S)) = Matrix.trace (W*L) := by
  have he : (T*W*S)*(T*L*S) = T*(W*L)*S := by
    calc
      _ = T*W*(S*T)*L*S := by noncomm_ring
      _ = _ := by rw [h]; noncomm_ring
  rw [he]
  calc
    _ = Matrix.trace (T*((W*L)*S)) := by rw [mul_assoc]
    _ = Matrix.trace (((W*L)*S)*T) := Matrix.trace_mul_comm _ _
    _ = _ := by rw [mul_assoc, h, mul_one]
theorem decoration_retains_sign (s t : ℝ)
    (h : Matrix.trace (W*(K*H s-1)) = Matrix.trace (W*(K*H t-1))) : s=t := by
  rw [decorated_parameter, decorated_parameter] at h
  linarith
#print axioms trace_transport
#print axioms decoration_retains_sign
#print axioms congruence
#print axioms inverse
#print axioms clifford_transport
#print axioms transported_square
#print axioms all_fields
#print axioms frozen_generator
#print axioms pencil_square
#print axioms decorated_parameter
end M09Transport
