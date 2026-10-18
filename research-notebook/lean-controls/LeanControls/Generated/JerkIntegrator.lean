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
namespace LeanControls.Generated.JerkIntegrator
open Matrix LeanControls.BernsteinCertificate
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
def P : Mat := !![(37 / 4), (31 / 4), 2; (31 / 4), 13, (13 / 4); 2, (13 / 4), (7 / 4)]
def transition (h : ℝ) : Mat := !![(-1 / 6) * h ^ 3 + 1, (-1 / 2) * h ^ 3 + 1 * h, (-1 / 2) * h ^ 3 + (1 / 2) * h ^ 2; (-1 / 2) * h ^ 2, (-3 / 2) * h ^ 2 + 1, (-3 / 2) * h ^ 2 + 1 * h; -1 * h, -3 * h, -3 * h + 1]
def residual (h : ℝ) : Mat := !![(-37 / 144) * h ^ 5 + (-31 / 24) * h ^ 4 + (-47 / 12) * h ^ 3 + (-1 / 6) * h ^ 2 + 6 * h + 3, (-37 / 48) * h ^ 5 + (-31 / 8) * h ^ 4 + (-245 / 24) * h ^ 3 + (1 / 24) * h ^ 2 + (119 / 8) * h, (-37 / 48) * h ^ 5 + (-149 / 48) * h ^ 4 + (-409 / 48) * h ^ 3 + (65 / 24) * h ^ 2 + (53 / 8) * h; (-37 / 48) * h ^ 5 + (-31 / 8) * h ^ 4 + (-245 / 24) * h ^ 3 + (1 / 24) * h ^ 2 + (119 / 8) * h, (-37 / 16) * h ^ 5 + (-93 / 8) * h ^ 4 + -26 * h ^ 3 + (7 / 4) * h ^ 2 + 26 * h + 3, (-37 / 16) * h ^ 5 + (-149 / 16) * h ^ 4 + (-335 / 16) * h ^ 3 + (41 / 8) * h ^ 2 + (51 / 4) * h; (-37 / 48) * h ^ 5 + (-149 / 48) * h ^ 4 + (-409 / 48) * h ^ 3 + (65 / 24) * h ^ 2 + (53 / 8) * h, (-37 / 16) * h ^ 5 + (-149 / 16) * h ^ 4 + (-335 / 16) * h ^ 3 + (41 / 8) * h ^ 2 + (51 / 4) * h, (-37 / 16) * h ^ 5 + -7 * h ^ 4 + (-291 / 16) * h ^ 3 + 10 * h ^ 2 + (-3 / 2) * h + 3]
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
def s0c1 : Mat := !![(18 / 5), (119 / 80), (53 / 80); (119 / 80), (28 / 5), (51 / 40); (53 / 80), (51 / 40), (57 / 20)]
theorem s0c1_psd : s0c1.PosSemidef := by
  apply psd_of_ldl s0c1 !![1, 0, 0; (119 / 288), 1, 0; (53 / 288), (23069 / 114863), 1] ![(18 / 5), (114863 / 23040), (1451288 / 574315)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c2 : Mat := !![(1007 / 240), (2857 / 960), (1337 / 960); (2857 / 960), (1319 / 160), (857 / 320); (1337 / 960), (857 / 320), (59 / 20)]
theorem s0c2_psd : s0c2.PosSemidef := by
  apply psd_of_ldl s0c2 !![1, 0, 0; (2857 / 4028), 1, 0; (1337 / 4028), (6536179 / 23715143), 1] ![(1007 / 240), (23715143 / 3866880), (95897243 / 47430286)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c3 : Mat := !![(4549 / 960), (8329 / 1920), (8003 / 3840); (8329 / 1920), (1697 / 160), (5053 / 1280); (8003 / 3840), (5053 / 1280), (3933 / 1280)]
theorem s0c3_psd : s0c3.PosSemidef := by
  apply psd_of_ldl s0c3 !![1, 0, 0; (8329 / 9098), 1, 0; (8003 / 18196), (71259595 / 231798862), 1] ![(4549 / 960), (115899431 / 17468160), (45365006093 / 29670254336)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c4 : Mat := !![(9913 / 1920), (10363 / 1920), (3317 / 1280); (10363 / 1920), (7819 / 640), (6023 / 1280); (3317 / 1280), (6023 / 1280), (929 / 320)]
theorem s0c4_psd : s0c4.PosSemidef := by
  apply psd_of_ldl s0c4 !![1, 0, 0; (10363 / 9913), 1, 0; (9951 / 19826), (9499473 / 31284368), 1] ![(9913 / 1920), (1955273 / 297390), (2493343909 / 2502749440)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c4, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c5 : Mat := !![(24791 / 4608), (9071 / 1536), (4157 / 1536); (9071 / 1536), (6343 / 512), (2245 / 512); (4157 / 1536), (2245 / 512), (1007 / 512)]
theorem s0c5_psd : s0c5.PosSemidef := by
  apply psd_of_ldl s0c5 !![1, 0, 0; (27213 / 24791), 1, 0; (12471 / 24791), (70108 / 292837), 1] ![(24791 / 4608), (292837 / 49582), (2500537 / 9370784)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c5, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def coeff0 (k : ℕ) : Mat :=
  match k with
  | 0 => s0c0
  | 1 => s0c1
  | 2 => s0c2
  | 3 => s0c3
  | 4 => s0c4
  | 5 => s0c5
  | _ => 0
theorem coeff0_psd (k : ℕ) (hk : k < 6) : (coeff0 k).PosSemidef := by
  interval_cases k
  · exact s0c0_psd
  · exact s0c1_psd
  · exact s0c2_psd
  · exact s0c3_psd
  · exact s0c4_psd
  · exact s0c5_psd
theorem identity0 (t : ℝ) : residual (0 + ((1 / 2) - 0) * t) = combination 5 coeff0 t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [residual, combination, weight, bernsteinPolynomial, Nat.choose, Finset.sum_range_succ, coeff0, s0c0, s0c1, s0c2, s0c3, s0c4, s0c5] <;> ring
theorem interval0 {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 2)) : (residual h).PosSemidef := by
  exact interval_psd 5 coeff0 residual (by norm_num) coeff0_psd identity0 hlo hhi
theorem residual_psd {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 2)) : (residual h).PosSemidef := by
  exact interval0 (by linarith) hhi
theorem residual_identity (h : ℝ) : P - (transition h).transpose * P * transition h - (h * 1) • (1 : Mat) = h • residual h := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P, transition, residual, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
theorem certified_decrease {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 2)) (x : Fin 3 → ℝ) :
    energy P (transition h *ᵥ x) ≤ energy P x - h * 1 * squaredNorm x := by
  apply step_decrease
  rw [residual_identity]
  exact (residual_psd hlo hhi).smul (by linarith)
theorem certified_contraction {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 2)) (x : Fin 3 → ℝ) :
    energy P (transition h *ᵥ x) ≤ (1 - h * 1 / upperBound) * energy P x := by
  apply contract_of_decrease P (transition h) (by linarith) (by norm_num) upper_pos upper_psd
  exact certified_decrease hlo hhi
theorem certified_jitter (h : ℕ → ℝ) (x : ℕ → Fin 3 → ℝ) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ (1 / 2))
    (hlo : ∀ k, hmin ≤ h k) (hhi : ∀ k, h k ≤ (1 / 2))
    (hdyn : ∀ k, x (k+1) = transition (h k) *ᵥ x k) (n : ℕ) :
    energy P (x n) ≤ (1 - hmin * 1 / upperBound) ^ n * energy P (x 0) := by
  apply jitter_energy P transition h x (by linarith) (by norm_num) upper_pos
    (by dsimp [upperBound]; nlinarith) P_psd upper_psd
    (fun t ht htmax => certified_decrease (by linarith) htmax) hlo hhi hdyn n
end LeanControls.Generated.JerkIntegrator
