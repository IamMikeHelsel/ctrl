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
namespace LeanControls.Generated.UncertainA1L1R2
open Matrix LeanControls.BernsteinCertificate
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
def P : Mat := !![(38 / 5), (257 / 25), 5; (257 / 25), (1319 / 50), (769 / 50); 5, (769 / 50), (278 / 25)]
def transition (h : ℝ) : Mat := !![(1 / 2) * h ^ 2 + 1, (3 / 2) * h ^ 2 + 1 * h, 2 * h ^ 2; (-11 / 10) * h ^ 2, (-33 / 10) * h ^ 2 + 1, (-33 / 10) * h ^ 2 + 1 * h; (121 / 100) * h ^ 2 + (-11 / 10) * h, (363 / 100) * h ^ 2 + (-33 / 10) * h, (363 / 100) * h ^ 2 + (-33 / 10) * h + 1]
def residual (h : ℝ) : Mat := !![(-487629 / 125000) * h ^ 3 + (-26477 / 12500) * h ^ 2 + (-6587 / 625) * h + (19 / 2), (-1462887 / 125000) * h ^ 3 + (-30603 / 6250) * h ^ 2 + (-126117 / 5000) * h + (12909 / 500), (-685881 / 62500) * h ^ 3 + (41593 / 25000) * h ^ 2 + (-54777 / 2500) * h + (4613 / 250); (-1462887 / 125000) * h ^ 3 + (-30603 / 6250) * h ^ 2 + (-126117 / 5000) * h + (12909 / 500), (-4388661 / 125000) * h ^ 3 + (-128943 / 12500) * h ^ 2 + (-160219 / 2500) * h + (9931 / 125), (-2057643 / 62500) * h ^ 3 + (139129 / 25000) * h ^ 2 + (-252849 / 5000) * h + (5607 / 100); (-685881 / 62500) * h ^ 3 + (41593 / 25000) * h ^ 2 + (-54777 / 2500) * h + (4613 / 250), (-2057643 / 62500) * h ^ 3 + (139129 / 25000) * h ^ 2 + (-252849 / 5000) * h + (5607 / 100), (-4079411 / 125000) * h ^ 3 + (58643 / 3125) * h ^ 2 + (-5649 / 125) * h + (10283 / 250)]
def lowerBound : ℝ := (11131832 / 13195175)
def upperBound : ℝ := (451 / 10)
theorem lower_pos : 0 < lowerBound := by norm_num [lowerBound]
theorem upper_pos : 0 < upperBound := by norm_num [upperBound]
theorem P_psd : (P).PosSemidef := by
  apply psd_of_ldl (P) !![1, 0, 0; (257 / 190), 1, 0; (25 / 38), (20465 / 29628), 1] ![(38 / 5), (29628 / 2375), (1391479 / 740700)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [P, lowerBound, upperBound, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
theorem lower_psd : (P - lowerBound • (1 : Mat)).PosSemidef := by
  apply psd_of_ldl (P - lowerBound • (1 : Mat)) !![1, 0, 0; (135646399 / 89151498), 1, 0; (65975875 / 89151498), (4571587427202271 / 5820132726460390), 1] ![(89151498 / 13195175), (1164026545292078 / 117636961762215), (18091069798066557450888 / 38398834924435988309125)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [P, lowerBound, upperBound, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
theorem upper_psd : (upperBound • (1 : Mat) - P).PosSemidef := by
  apply psd_of_ldl (upperBound • (1 : Mat) - P) !![1, 0, 0; (-514 / 1875), 1, 0; (-2 / 15), (-1570375 / 1490804), 1] ![(75 / 2), (745402 / 46875), (1167941121 / 74540200)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [P, lowerBound, upperBound, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
theorem certified_energy_bounds (x : Fin 3 → ℝ) :
    lowerBound * squaredNorm x ≤ energy P x ∧ energy P x ≤ upperBound * squaredNorm x :=
  energy_bounds P lower_psd upper_psd x
def s0c0 : Mat := !![(19 / 2), (12909 / 500), (4613 / 250); (12909 / 500), (9931 / 125), (5607 / 100); (4613 / 250), (5607 / 100), (10283 / 250)]
theorem s0c0_psd : s0c0.PosSemidef := by
  apply psd_of_ldl s0c0 !![1, 0, 0; (12909 / 4750), 1, 0; (4613 / 2375), (14067816 / 22046719), 1] ![(19 / 2), (22046719 / 2375000), (833801178 / 551167975)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c1 : Mat := !![(164951 / 18750), (603411 / 25000), (212391 / 12500); (603411 / 25000), (2819081 / 37500), (1317467 / 25000); (212391 / 12500), (1317467 / 25000), (47649 / 1250)]
theorem s0c1_psd : s0c1.PosSemidef := by
  apply psd_of_ldl s0c1 !![1, 0, 0; (1810233 / 659804), 1, 0; (637173 / 329902), (300946806786 / 443138325959), 1] ![(164951 / 18750), (443138325959 / 49485300000), (129850084524327 / 110784581489750)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c2 : Mat := !![(2520791 / 312500), (1749187 / 78125), (29161393 / 1875000); (1749187 / 78125), (66342607 / 937500), (92627929 / 1875000); (29161393 / 1875000), (92627929 / 1875000), (16573411 / 468750)]
theorem s0c2_psd : s0c2.PosSemidef := by
  apply psd_of_ldl s0c2 !![1, 0, 0; (6996748 / 2520791), 1, 0; (29161393 / 15124746), (9427434119 / 13038335306), 1] ![(2520791 / 312500), (6519167653 / 756237300), (633022063347943 / 733406360962500)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c3 : Mat := !![(113691021 / 15625000), (160029969 / 7812500), (219509313 / 15625000); (160029969 / 7812500), (1030265439 / 15625000), (89678258 / 1953125); (219509313 / 15625000), (89678258 / 1953125), (509111689 / 15625000)]
theorem s0c3_psd : s0c3.PosSemidef := by
  apply psd_of_ldl s0c3 !![1, 0, 0; (106686646 / 37897007), 1, 0; (73169771 / 37897007), (241253644778 / 313462735965), 1] ![(113691021 / 15625000), (62692547193 / 7579401400), (21911700065159 / 39182841995625)]
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
theorem residual_identity (h : ℝ) : P - (transition h).transpose * P * transition h - (h * (3 / 2)) • (1 : Mat) = h • residual h := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P, transition, residual, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
theorem certified_decrease {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) (x : Fin 3 → ℝ) :
    energy P (transition h *ᵥ x) ≤ energy P x - h * (3 / 2) * squaredNorm x := by
  apply step_decrease
  rw [residual_identity]
  exact (residual_psd hlo hhi).smul (by linarith)
theorem certified_contraction {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) (x : Fin 3 → ℝ) :
    energy P (transition h *ᵥ x) ≤ (1 - h * (3 / 2) / upperBound) * energy P x := by
  apply contract_of_decrease P (transition h) (by linarith) (by norm_num) upper_pos upper_psd
  exact certified_decrease hlo hhi
theorem certified_jitter (h : ℕ → ℝ) (x : ℕ → Fin 3 → ℝ) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ (1 / 5))
    (hlo : ∀ k, hmin ≤ h k) (hhi : ∀ k, h k ≤ (1 / 5))
    (hdyn : ∀ k, x (k+1) = transition (h k) *ᵥ x k) (n : ℕ) :
    energy P (x n) ≤ (1 - hmin * (3 / 2) / upperBound) ^ n * energy P (x 0) := by
  apply jitter_energy P transition h x (by linarith) (by norm_num) upper_pos
    (by dsimp [upperBound]; nlinarith) P_psd upper_psd
    (fun t ht htmax => certified_decrease (by linarith) htmax) hlo hhi hdyn n
end LeanControls.Generated.UncertainA1L1R2

