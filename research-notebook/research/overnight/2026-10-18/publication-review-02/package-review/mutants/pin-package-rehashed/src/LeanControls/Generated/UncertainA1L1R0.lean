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
namespace LeanControls.Generated.UncertainA1L1R0
open Matrix LeanControls.BernsteinCertificate
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
def P : Mat := !![(38 / 5), (257 / 25), 5; (257 / 25), (1319 / 50), (769 / 50); 5, (769 / 50), (278 / 25)]
def transition (h : ℝ) : Mat := !![(1 / 2) * h ^ 2 + 1, (3 / 2) * h ^ 2 + 1 * h, 2 * h ^ 2; (-9 / 10) * h ^ 2, (-27 / 10) * h ^ 2 + 1, (-27 / 10) * h ^ 2 + 1 * h; (81 / 100) * h ^ 2 + (-9 / 10) * h, (243 / 100) * h ^ 2 + (-27 / 10) * h, (243 / 100) * h ^ 2 + (-27 / 10) * h + 1]
def residual (h : ℝ) : Mat := !![(-367199 / 125000) * h ^ 3 + (-52533 / 12500) * h ^ 2 + (-3877 / 625) * h + (15 / 2), (-1101597 / 125000) * h ^ 3 + (-70037 / 6250) * h ^ 2 + (-60857 / 5000) * h + (9871 / 500), (-253493 / 31250) * h ^ 3 + (-105343 / 25000) * h ^ 2 + (-26097 / 2500) * h + (3307 / 250); (-1101597 / 125000) * h ^ 3 + (-70037 / 6250) * h ^ 2 + (-60857 / 5000) * h + (9871 / 500), (-3304791 / 125000) * h ^ 3 + (-367647 / 12500) * h ^ 2 + (-61999 / 2500) * h + (7624 / 125), (-760479 / 31250) * h ^ 3 + (-305879 / 25000) * h ^ 2 + (-80109 / 5000) * h + (4017 / 100); (-253493 / 31250) * h ^ 3 + (-105343 / 25000) * h ^ 2 + (-26097 / 2500) * h + (3307 / 250), (-760479 / 31250) * h ^ 3 + (-305879 / 25000) * h ^ 2 + (-80109 / 5000) * h + (4017 / 100), (-3016541 / 125000) * h ^ 3 + (7067 / 3125) * h ^ 2 + (-1923 / 125) * h + (6947 / 250)]
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
def s0c0 : Mat := !![(15 / 2), (9871 / 500), (3307 / 250); (9871 / 500), (7624 / 125), (4017 / 100); (3307 / 250), (4017 / 100), (6947 / 250)]
theorem s0c0_psd : s0c0.PosSemidef := by
  apply psd_of_ldl s0c0 !![1, 0, 0; (9871 / 3750), 1, 0; (3307 / 1875), (10031956 / 16923359), 1] ![(15 / 2), (16923359 / 1875000), (543958658 / 423083975)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c1 : Mat := !![(132871 / 18750), (1419793 / 75000), (156651 / 12500); (1419793 / 75000), (2225201 / 37500), (977547 / 25000); (156651 / 12500), (977547 / 25000), (33453 / 1250)]
theorem s0c1_psd : s0c1.PosSemidef := by
  apply psd_of_ldl s0c1 !![1, 0, 0; (1419793 / 531484), 1, 0; (469953 / 265742), (74726603262 / 116501764573), 1] ![(132871 / 18750), (116501764573 / 13287100000), (28910604523149 / 29125441143250)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c2 : Mat := !![(6203317 / 937500), (2807771 / 156250), (22087457 / 1875000); (2807771 / 156250), (53712403 / 937500), (71007421 / 1875000); (22087457 / 1875000), (71007421 / 1875000), (12078259 / 468750)]
theorem s0c2_psd : s0c2.PosSemidef := by
  apply psd_of_ldl s0c2 !![1, 0, 0; (990978 / 364901), 1, 0; (22087457 / 12406634), (32179959739 / 46481181230), 1] ![(6203317 / 937500), (4648118123 / 547351500), (5727373872397 / 7901800809100)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c3 : Mat := !![(94808651 / 15625000), (65581957 / 3906250), (170418703 / 15625000); (65581957 / 3906250), (853814109 / 15625000), (283449617 / 7812500); (170418703 / 15625000), (283449617 / 7812500), (384509359 / 15625000)]
theorem s0c3_psd : s0c3.PosSemidef := by
  apply psd_of_ldl s0c3 !![1, 0, 0; (37475404 / 13544093), 1, 0; (24345529 / 13544093), (82664076982 / 110930967185), 1] ![(94808651 / 15625000), (22186193437 / 2708818600), (6316191192331 / 13866370898125)]
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
end LeanControls.Generated.UncertainA1L1R0

