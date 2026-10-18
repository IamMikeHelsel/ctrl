module
public import LeanControls.BernsteinCertificate
public import Mathlib.LinearAlgebra.Matrix.Notation
-- Uniform generated tactics may contain unused simplification rules.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public section
noncomputable section
namespace LeanControls.Generated.LagLower
open Matrix LeanControls.BernsteinCertificate
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
def P : Mat := !![(37 / 4), (31 / 4), 2; (31 / 4), 13, (13 / 4); 2, (13 / 4), (7 / 4)]
def transition (h : ℝ) : Mat := !![(-1 / 2) * h ^ 2 + 1, (-3 / 2) * h ^ 2 + 1 * h, -1 * h ^ 2; 0, 1, 1 * h; -1 * h, -3 * h, -3 * h + 1]
def residual (h : ℝ) : Mat := !![(-37 / 16) * h ^ 3 + -2 * h ^ 2 + (15 / 2) * h + 3, (-111 / 16) * h ^ 3 + (-11 / 8) * h ^ 2 + (29 / 2) * h, (-37 / 8) * h ^ 3 + (-9 / 8) * h ^ 2 + (33 / 4) * h; (-111 / 16) * h ^ 3 + (-11 / 8) * h ^ 2 + (29 / 2) * h, (-333 / 16) * h ^ 3 + (39 / 4) * h ^ 2 + (41 / 4) * h + 3, (-111 / 8) * h ^ 3 + (47 / 8) * h ^ 2 + 3 * h; (-37 / 8) * h ^ 3 + (-9 / 8) * h ^ 2 + (33 / 4) * h, (-111 / 8) * h ^ 3 + (47 / 8) * h ^ 2 + 3 * h, (-37 / 4) * h ^ 3 + (7 / 2) * h ^ 2 + (-21 / 4) * h + 3]
def lowerBound : ℝ := (2 / 3)
def upperBound : ℝ := 24
theorem lower_pos : 0 < lowerBound := by norm_num [lowerBound]
theorem upper_pos : 0 < upperBound := by norm_num [upperBound]
theorem P_psd : (P).PosSemidef := by
  apply psd_of_ldl (P) !![1, 0, 0; (31 / 37), 1, 0; (8 / 37), (233 / 963), 1] ![(37 / 4), (963 / 148), (902 / 963)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [P, lowerBound, upperBound, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
theorem lower_psd : (P - lowerBound • (1 : Mat)).PosSemidef := by
  apply psd_of_ldl (P - lowerBound • (1 : Mat)) !![1, 0, 0; (93 / 103), 1, 0; (24 / 103), (357 / 1319), 1] ![(103 / 12), (6595 / 1236), (896 / 3957)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [P, lowerBound, upperBound, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
theorem upper_psd : (upperBound • (1 : Mat) - P).PosSemidef := by
  apply psd_of_ldl (upperBound • (1 : Mat) - P) !![1, 0, 0; (-31 / 59), 1, 0; (-8 / 59), (-203 / 327), 1] ![(59 / 4), (1635 / 236), (6314 / 327)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [P, lowerBound, upperBound, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
theorem certified_energy_bounds (x : Fin 3 → ℝ) :
    lowerBound * squaredNorm x ≤ energy P x ∧ energy P x ≤ upperBound * squaredNorm x :=
  energy_bounds P lower_psd upper_psd x
def s0c0 : Mat := !![3, 0, 0; 0, 3, 0; 0, 0, 3]
theorem s0c0_psd : s0c0.PosSemidef := by
  apply psd_of_ldl s0c0 !![1, 0, 0; 0, 1, 0; 0, 0, 1] ![3, 3, 3]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c1 : Mat := !![(7 / 2), (29 / 30), (11 / 20); (29 / 30), (221 / 60), (1 / 5); (11 / 20), (1 / 5), (53 / 20)]
theorem s0c1_psd : s0c1.PosSemidef := by
  apply psd_of_ldl s0c1 !![1, 0, 0; (29 / 105), 1, 0; (11 / 70), (303 / 21523), 1] ![(7 / 2), (21523 / 6300), (2206447 / 860920)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c2 : Mat := !![(298 / 75), (383 / 200), (217 / 200); (383 / 200), (1349 / 300), (287 / 600); (217 / 200), (287 / 600), (176 / 75)]
theorem s0c2_psd : s0c2.PosSemidef := by
  apply psd_of_ldl s0c2 !![1, 0, 0; (1149 / 2384), 1, 0; (651 / 2384), (-63791 / 5111831), 1] ![(298 / 75), (5111831 / 1430400), (52391889 / 25559155)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c3 : Mat := !![(8803 / 2000), (5579 / 2000), (196 / 125); (5579 / 2000), (10547 / 2000), (181 / 250); (196 / 125), (181 / 250), (252 / 125)]
theorem s0c3_psd : s0c3.PosSemidef := by
  apply psd_of_ldl s0c3 !![1, 0, 0; (5579 / 8803), 1, 0; (3136 / 8803), (-4749 / 61720), 1] ![(8803 / 2000), (30860 / 8803), (177341 / 123440)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def coeff0 (k : ℕ) : Mat :=
  match k with
  | 0 => s0c0
  | 1 => s0c1
  | 2 => s0c2
  | 3 => s0c3
  | _ => 0
theorem coeff0_psd (k : ℕ) (hk : k < 4) : (coeff0 k).PosSemidef := by
  interval_cases k
  · exact s0c0_psd
  · exact s0c1_psd
  · exact s0c2_psd
  · exact s0c3_psd
theorem identity0 (t : ℝ) : residual (0 + ((1 / 5) - 0) * t) = combination 3 coeff0 t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [residual, combination, weight, bernsteinPolynomial, Nat.choose, Finset.sum_range_succ, coeff0, s0c0, s0c1, s0c2, s0c3] <;> ring
theorem interval0 {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) : (residual h).PosSemidef := by
  exact interval_psd 3 coeff0 residual (by norm_num) coeff0_psd identity0 hlo hhi
theorem residual_psd {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) : (residual h).PosSemidef := by
  exact interval0 (by linarith) hhi
theorem residual_identity (h : ℝ) : P - (transition h).transpose * P * transition h - (h * 1) • (1 : Mat) = h • residual h := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P, transition, residual, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
theorem certified_decrease {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) (x : Fin 3 → ℝ) :
    energy P (transition h *ᵥ x) ≤ energy P x - h * 1 * squaredNorm x := by
  apply step_decrease
  rw [residual_identity]
  exact (residual_psd hlo hhi).smul (by linarith)
theorem certified_contraction {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) (x : Fin 3 → ℝ) :
    energy P (transition h *ᵥ x) ≤ (1 - h * 1 / upperBound) * energy P x := by
  apply contract_of_decrease P (transition h) (by linarith) (by norm_num) upper_pos upper_psd
  exact certified_decrease hlo hhi
theorem certified_jitter (h : ℕ → ℝ) (x : ℕ → Fin 3 → ℝ) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ (1 / 5))
    (hlo : ∀ k, hmin ≤ h k) (hhi : ∀ k, h k ≤ (1 / 5))
    (hdyn : ∀ k, x (k+1) = transition (h k) *ᵥ x k) (n : ℕ) :
    energy P (x n) ≤ (1 - hmin * 1 / upperBound) ^ n * energy P (x 0) := by
  apply jitter_energy P transition h x (by linarith) (by norm_num) upper_pos
    (by dsimp [upperBound]; nlinarith) P_psd upper_psd
    (fun t ht htmax => certified_decrease (by linarith) htmax) hlo hhi hdyn n
end LeanControls.Generated.LagLower
