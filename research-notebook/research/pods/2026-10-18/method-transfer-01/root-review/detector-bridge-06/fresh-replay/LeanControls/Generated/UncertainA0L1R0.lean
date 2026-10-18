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
namespace LeanControls.Generated.UncertainA0L1R0
open Matrix LeanControls.BernsteinCertificate
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
def P : Mat := !![(38 / 5), (257 / 25), 5; (257 / 25), (1319 / 50), (769 / 50); 5, (769 / 50), (278 / 25)]
def transition (h : ℝ) : Mat := !![(1 / 5) * h ^ 2 + 1, (3 / 5) * h ^ 2 + 1 * h, (7 / 5) * h ^ 2; (-9 / 25) * h ^ 2, (-27 / 25) * h ^ 2 + 1, (-81 / 50) * h ^ 2 + 1 * h; (81 / 250) * h ^ 2 + (-9 / 25) * h, (243 / 250) * h ^ 2 + (-27 / 25) * h, (729 / 500) * h ^ 2 + (-81 / 50) * h + 1]
def residual (h : ℝ) : Mat := !![(-367199 / 781250) * h ^ 3 + (-52533 / 78125) * h ^ 2 + (-4993 / 15625) * h + (21 / 10), (-1101597 / 781250) * h ^ 3 + (-227573 / 156250) * h ^ 2 + (101039 / 62500) * h + (4171 / 1250), (-1433333 / 781250) * h ^ 3 + (103681 / 312500) * h ^ 2 + (-80679 / 62500) * h + (2279 / 1250); (-1101597 / 781250) * h ^ 3 + (-227573 / 156250) * h ^ 2 + (101039 / 62500) * h + (4171 / 1250), (-3304791 / 781250) * h ^ 3 + (-209922 / 78125) * h ^ 2 + (155491 / 31250) * h + (13951 / 1250), (-4299999 / 781250) * h ^ 3 + (-21958 / 78125) * h ^ 2 + (462021 / 125000) * h + (13863 / 2500); (-1433333 / 781250) * h ^ 3 + (103681 / 312500) * h ^ 2 + (-80679 / 62500) * h + (2279 / 1250), (-4299999 / 781250) * h ^ 3 + (-21958 / 78125) * h ^ 2 + (462021 / 125000) * h + (13863 / 2500), (-27794369 / 3125000) * h ^ 3 + (987901 / 156250) * h ^ 2 + (-36357 / 15625) * h + (4711 / 1250)]
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
def s0c0 : Mat := !![(21 / 10), (4171 / 1250), (2279 / 1250); (4171 / 1250), (13951 / 1250), (13863 / 2500); (2279 / 1250), (13863 / 2500), (4711 / 1250)]
theorem s0c0_psd : s0c0.PosSemidef := by
  apply psd_of_ldl s0c0 !![1, 0, 0; (4171 / 2625), 1, 0; (2279 / 2625), (17378957 / 38448268), 1] ![(21 / 10), (9612067 / 1640625), (3802131391 / 3844826800)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c1 : Mat := !![(974389 / 468750), (3229289 / 937500), (542857 / 312500); (3229289 / 937500), (2693558 / 234375), (3619757 / 625000); (542857 / 312500), (3619757 / 625000), (564637 / 156250)]
theorem s0c1_psd : s0c1.PosSemidef := by
  apply psd_of_ldl s0c1 !![1, 0, 0; (3229289 / 1948778), 1, 0; (1628571 / 1948778), (23653456864 / 46970128191), 1] ![(974389 / 468750), (140910384573 / 24359725000), (10881626386689 / 15656709397000)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c2 : Mat := !![(24005009 / 11718750), (13800509 / 3906250), (38800981 / 23437500); (13800509 / 3906250), (138145331 / 11718750), (70714159 / 11718750); (38800981 / 23437500), (70714159 / 11718750), (20758913 / 5859375)]
theorem s0c2_psd : s0c2.PosSemidef := by
  apply psd_of_ldl s0c2 !![1, 0, 0; (41401527 / 24005009), 1, 0; (38800981 / 48010018), (572341818863 / 1025339824660), 1] ![(24005009 / 11718750), (51266991233 / 9001878375), (8825732665499 / 20506796493200)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c3 : Mat := !![(97921513 / 48828125), (701286281 / 195312500), (152697367 / 97656250); (701286281 / 195312500), (1173302859 / 97656250), (2433265279 / 390625000); (152697367 / 97656250), (2433265279 / 390625000), (1361398231 / 390625000)]
theorem s0c3_psd : s0c3.PosSemidef := by
  apply psd_of_ldl s0c3 !![1, 0, 0; (701286281 / 391686052), 1, 0; (152697367 / 195843026), (671664379024 / 1093965520295), 1] ![(97921513 / 48828125), (218793104059 / 39168605200), (175420812696611 / 1093965520295000)]
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
end LeanControls.Generated.UncertainA0L1R0

