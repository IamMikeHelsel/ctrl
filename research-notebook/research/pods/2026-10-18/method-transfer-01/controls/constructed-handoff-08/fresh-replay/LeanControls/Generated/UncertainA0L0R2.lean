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
namespace LeanControls.Generated.UncertainA0L0R2
open Matrix LeanControls.BernsteinCertificate
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
def P : Mat := !![(38 / 5), (257 / 25), 5; (257 / 25), (1319 / 50), (769 / 50); 5, (769 / 50), (278 / 25)]
def transition (h : ℝ) : Mat := !![(-1 / 5) * h ^ 2 + 1, (-3 / 5) * h ^ 2 + 1 * h, (-2 / 5) * h ^ 2; 0, 1, 1 * h; (-11 / 25) * h, (-33 / 25) * h, (-99 / 50) * h + 1]
def residual (h : ℝ) : Mat := !![(-38 / 125) * h ^ 3 + (-22 / 25) * h ^ 2 + (13862 / 15625) * h + (29 / 10), (-114 / 125) * h ^ 3 + (-28 / 25) * h ^ 2 + (36836 / 15625) * h + (7209 / 1250), (-76 / 125) * h ^ 3 + (-201 / 250) * h ^ 2 + (34983 / 31250) * h + (5641 / 1250); (-114 / 125) * h ^ 3 + (-28 / 25) * h ^ 2 + (36836 / 15625) * h + (7209 / 1250), (-342 / 125) * h ^ 3 + (6 / 5) * h ^ 2 + (-22492 / 15625) * h + (23179 / 1250), (-228 / 125) * h ^ 3 + (157 / 250) * h ^ 2 + (-31713 / 15625) * h + (34377 / 2500); (-76 / 125) * h ^ 3 + (-201 / 250) * h ^ 2 + (34983 / 31250) * h + (5641 / 1250), (-228 / 125) * h ^ 3 + (157 / 250) * h ^ 2 + (-31713 / 15625) * h + (34377 / 2500), (-152 / 125) * h ^ 3 + (38 / 125) * h ^ 2 + (-158439 / 31250) * h + (14719 / 1250)]
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
def s0c1 : Mat := !![(1387099 / 468750), (2777047 / 468750), (358393 / 78125); (2777047 / 468750), (8647141 / 468750), (4254841 / 312500); (358393 / 78125), (4254841 / 312500), (893531 / 78125)]
theorem s0c1_psd : s0c1.PosSemidef := by
  apply psd_of_ldl s0c1 !![1, 0, 0; (396721 / 198157), 1, 0; (307194 / 198157), (146345819 / 217521300), 1] ![(1387099 / 468750), (6525639 / 990785), (48733523827 / 36253550000)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c2 : Mat := !![(1409323 / 468750), (2843719 / 468750), (363386 / 78125); (2843719 / 468750), (8609657 / 468750), (12645521 / 937500); (363386 / 78125), (12645521 / 937500), (5204647 / 468750)]
theorem s0c2_psd : s0c2.PosSemidef := by
  apply psd_of_ldl s0c2 !![1, 0, 0; (2843719 / 1409323), 1, 0; (2180316 / 1409323), (1734787687 / 2590111924), 1] ![(1409323 / 468750), (647527981 / 105699225), (7505837979871 / 6475279810000)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c3 : Mat := !![(474969 / 156250), (966657 / 156250), (734323 / 156250); (966657 / 156250), (2856471 / 156250), (4173563 / 312500); (734323 / 156250), (4173563 / 312500), (840908 / 78125)]
theorem s0c3_psd : s0c3.PosSemidef := by
  apply psd_of_ldl s0c3 !![1, 0, 0; (322219 / 158323), 1, 0; (734323 / 474969), (100024197 / 150154460), 1] ![(474969 / 156250), (22523169 / 3958075), (219066320957 / 225231690000)]
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
end LeanControls.Generated.UncertainA0L0R2

