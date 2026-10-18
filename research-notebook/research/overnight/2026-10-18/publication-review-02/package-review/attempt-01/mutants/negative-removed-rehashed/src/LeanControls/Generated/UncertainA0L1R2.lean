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
namespace LeanControls.Generated.UncertainA0L1R2
open Matrix LeanControls.BernsteinCertificate
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
def P : Mat := !![(38 / 5), (257 / 25), 5; (257 / 25), (1319 / 50), (769 / 50); 5, (769 / 50), (278 / 25)]
def transition (h : ℝ) : Mat := !![(1 / 5) * h ^ 2 + 1, (3 / 5) * h ^ 2 + 1 * h, (7 / 5) * h ^ 2; (-11 / 25) * h ^ 2, (-33 / 25) * h ^ 2 + 1, (-99 / 50) * h ^ 2 + 1 * h; (121 / 250) * h ^ 2 + (-11 / 25) * h, (363 / 250) * h ^ 2 + (-33 / 25) * h, (1089 / 500) * h ^ 2 + (-99 / 50) * h + 1]
def residual (h : ℝ) : Mat := !![(-487629 / 781250) * h ^ 3 + (-26477 / 78125) * h ^ 2 + (-15413 / 15625) * h + (29 / 10), (-1462887 / 781250) * h ^ 3 + (-67737 / 156250) * h ^ 2 + (-25101 / 62500) * h + (7209 / 1250), (-983259 / 390625) * h ^ 3 + (525689 / 312500) * h ^ 2 + (-231939 / 62500) * h + (5641 / 1250); (-1462887 / 781250) * h ^ 3 + (-67737 / 156250) * h ^ 2 + (-25101 / 62500) * h + (7209 / 1250), (-4388661 / 781250) * h ^ 3 + (35082 / 78125) * h ^ 2 + (-35369 / 31250) * h + (23179 / 1250), (-2949777 / 390625) * h ^ 3 + (302423 / 78125) * h ^ 2 + (-455439 / 125000) * h + (34377 / 2500); (-983259 / 390625) * h ^ 3 + (525689 / 312500) * h ^ 2 + (-231939 / 62500) * h + (5641 / 1250), (-2949777 / 390625) * h ^ 3 + (302423 / 78125) * h ^ 2 + (-455439 / 125000) * h + (34377 / 2500), (-37234199 / 3125000) * h ^ 3 + (1831669 / 156250) * h ^ 2 + (-165687 / 15625) * h + (14719 / 1250)]
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
def s0c0 : Mat := !![(29 / 10), (7209 / 1250), (5641 / 1250); (7209 / 1250), (23179 / 1250), (34377 / 2500); (5641 / 1250), (34377 / 2500), (14719 / 1250)]
theorem s0c0_psd : s0c0.PosSemidef := by
  apply psd_of_ldl s0c0 !![1, 0, 0; (7209 / 3625), 1, 0; (5641 / 3625), (43284687 / 64108388), 1] ![(29 / 10), (16027097 / 2265625), (9794730831 / 6410838800)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c1 : Mat := !![(1328549 / 468750), (1793883 / 312500), (1332937 / 312500); (1793883 / 312500), (4328378 / 234375), (8442437 / 625000); (1332937 / 312500), (8442437 / 625000), (1729417 / 156250)]
theorem s0c1_psd : s0c1.PosSemidef := by
  apply psd_of_ldl s0c1 !![1, 0, 0; (5381649 / 2657098), 1, 0; (3998811 / 2657098), (485135059296 / 681662085959), 1] ![(1328549 / 468750), (681662085959 / 99641175000), (807037949310443 / 681662085959000)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c2 : Mat := !![(10796707 / 3906250), (22296371 / 3906250), (94697489 / 23437500); (22296371 / 3906250), (215604839 / 11718750), (78027023 / 5859375); (94697489 / 23437500), (78027023 / 5859375), (61626797 / 5859375)]
theorem s0c2_psd : s0c2.PosSemidef := by
  apply psd_of_ldl s0c2 !![1, 0, 0; (22296371 / 10796707), 1, 0; (94697489 / 64780242), (16106614709 / 21412807556), 1] ![(10796707 / 3906250), (5353201889 / 809753025), (2097705522277061 / 2408940850050000)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c3 : Mat := !![(131062698 / 48828125), (1104405501 / 195312500), (186413391 / 48828125); (1104405501 / 195312500), (1786119189 / 97656250), (5123643259 / 390625000); (186413391 / 48828125), (5123643259 / 390625000), (3917185201 / 390625000)]
theorem s0c3_psd : s0c3.PosSemidef := by
  apply psd_of_ldl s0c3 !![1, 0, 0; (368135167 / 174750264), 1, 0; (20712599 / 14562522), (147778309776 / 185752828655), 1] ![(131062698 / 48828125), (37150565731 / 5825008800), (104262094862099 / 185752828655000)]
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
end LeanControls.Generated.UncertainA0L1R2

