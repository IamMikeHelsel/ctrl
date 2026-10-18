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
namespace LeanControls.Generated.CoupledPlanar
open Matrix LeanControls.BernsteinCertificate
abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ
def P : Mat := !![(506991 / 95123), (-78091 / 95123), (111700 / 95123), (-66308 / 95123); (-78091 / 95123), (604685 / 95123), (-48380 / 95123), (214436 / 95123); (111700 / 95123), (-48380 / 95123), (103856 / 95123), (-38488 / 95123); (-66308 / 95123), (214436 / 95123), (-38488 / 95123), (1936 / 889)]
def transition (h : ℝ) : Mat := !![-1 * h ^ 2 + 1, (-1 / 4) * h ^ 2, (-3 / 2) * h ^ 2 + 1 * h, (-1 / 8) * h ^ 2; (-1 / 4) * h ^ 2, (-1 / 2) * h ^ 2 + 1, (-1 / 8) * h ^ 2, -1 * h ^ 2 + 1 * h; -2 * h, (-1 / 2) * h, -3 * h + 1, (-1 / 4) * h; (-1 / 2) * h, -1 * h, (-1 / 4) * h, -2 * h + 1]
def residual (h : ℝ) : Mat := !![(-8091813 / 1521968) * h ^ 3 + (-55103 / 13589) * h ^ 2 + (1169401 / 190246) * h + 3, (-2534515 / 1521968) * h ^ 3 + (-12842 / 13589) * h ^ 2 + (79897 / 190246) * h, (-23690797 / 3043936) * h ^ 3 + (-54199 / 54356) * h ^ 2 + (3748177 / 760984) * h, (-4288441 / 3043936) * h ^ 3 + (177 / 428) * h ^ 2 + (-938201 / 760984) * h; (-2534515 / 1521968) * h ^ 3 + (-12842 / 13589) * h ^ 2 + (79897 / 190246) * h, (-2613367 / 1521968) * h ^ 3 + (-26431 / 13589) * h ^ 2 + (742023 / 190246) * h + 3, (-5340987 / 3043936) * h ^ 3 + (26139 / 54356) * h ^ 2 + (-1084567 / 760984) * h, (-9401041 / 3043936) * h ^ 3 + (-50477 / 54356) * h ^ 2 + (3973077 / 760984) * h; (-23690797 / 3043936) * h ^ 3 + (-54199 / 54356) * h ^ 2 + (3748177 / 760984) * h, (-5340987 / 3043936) * h ^ 3 + (26139 / 54356) * h ^ 2 + (-1084567 / 760984) * h, (-71737205 / 6087872) * h ^ 3 + (81252 / 13589) * h ^ 2 + (-436859 / 95123) * h + 3, (-3346545 / 6087872) * h ^ 3 + (14341 / 13589) * h ^ 2 + (-346681 / 190246) * h; (-4288441 / 3043936) * h ^ 3 + (177 / 428) * h ^ 2 + (-938201 / 760984) * h, (-9401041 / 3043936) * h ^ 3 + (-50477 / 54356) * h ^ 2 + (3973077 / 760984) * h, (-3346545 / 6087872) * h ^ 3 + (14341 / 13589) * h ^ 2 + (-346681 / 190246) * h, (-37957375 / 6087872) * h ^ 3 + (54638 / 13589) * h ^ 2 + (-155447 / 95123) * h + 3]
def lowerBound : ℝ := (2 / 5)
def upperBound : ℝ := (1422684 / 95123)
theorem lower_pos : 0 < lowerBound := by norm_num [lowerBound]
theorem upper_pos : 0 < upperBound := by norm_num [upperBound]
theorem P_psd : (P).PosSemidef := by
  apply psd_of_ldl (P) !![1, 0, 0, 0; (-78091 / 506991), 1, 0, 0; (111700 / 506991), (-1128961420 / 21462260611), 1, 0; (-66308 / 506991), (7395647432 / 21462260611), (-370492637 / 2188757724), 1] ![(506991 / 95123), (42924521222 / 6889500699), (17510061792 / 21462260611), (724136506 / 547189431)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [P, lowerBound, upperBound, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
theorem lower_psd : (P - lowerBound • (1 : Mat)).PosSemidef := by
  apply psd_of_ldl (P - lowerBound • (1 : Mat)) !![1, 0, 0, 0; (-390455 / 2344709), 1, 0, 0; (558500 / 2344709), (-24936856400 / 463608942349), 1, 0; (-331540 / 2344709), (170321331780 / 463608942349), (-143209298860 / 458118007971), 1] ![(2344709 / 475615), (927217884698 / 159311253005), (916236015942 / 2318044711745), (1958439714778 / 2290590039855)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [P, lowerBound, upperBound, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
theorem upper_psd : (upperBound • (1 : Mat) - P).PosSemidef := by
  apply psd_of_ldl (upperBound • (1 : Mat) - P) !![1, 0, 0, 0; (78091 / 915693), 1, 0, 0; (-111700 / 915693), (26511996020 / 371468877013), 1, 0; (66308 / 915693), (-100767801088 / 371468877013), (5784193727454146 / 120826715079051291), 1] ![(915693 / 95123), (742937754026 / 87103465239), (483306860316205164 / 35335233988107599), (19816359254528416162172 / 1641914231209227993399)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [P, lowerBound, upperBound, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
theorem certified_energy_bounds (x : Fin 4 → ℝ) :
    lowerBound * squaredNorm x ≤ energy P x ∧ energy P x ≤ upperBound * squaredNorm x :=
  energy_bounds P lower_psd upper_psd x
def s0c0 : Mat := !![3, 0, 0, 0; 0, 3, 0, 0; 0, 0, 3, 0; 0, 0, 0, 3]
theorem s0c0_psd : s0c0.PosSemidef := by
  apply psd_of_ldl s0c0 !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] ![3, 3, 3, 3]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c1 : Mat := !![(8018257 / 2282952), (79897 / 2282952), (3748177 / 9131808), (-938201 / 9131808); (79897 / 2282952), (2530293 / 760984), (-1084567 / 9131808), (1324359 / 3043936); (3748177 / 9131808), (-1084567 / 9131808), (2987569 / 1141476), (-346681 / 2282952); (-938201 / 9131808), (1324359 / 3043936), (-346681 / 2282952), (3268981 / 1141476)]
theorem s0c1_psd : s0c1.PosSemidef := by
  apply psd_of_ldl s0c1 !![1, 0, 0, 0; (79897 / 8018257), 1, 0, 0; (3748177 / 32073028), (-1124475629686 / 30429617573647), 1, 0; (-938201 / 32073028), (15966055956043 / 121718470294588), (-19647419132114493519 / 407253781135904609303), 1] ![(8018257 / 2282952), (30429617573647 / 9152647927332), (407253781135904609303 / 158787100111983007872), (2972662818155672075804216105 / 1062560953316315085277145664)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c2 : Mat := !![(17989595 / 4565904), (114847 / 2282952), (4871105 / 6087872), (-3595451 / 18263616); (114847 / 2282952), (16480787 / 4565904), (-4155295 / 18263616), (15538969 / 18263616); (4871105 / 6087872), (-4155295 / 18263616), (2692901 / 1141476), (-428779 / 1521968); (-3595451 / 18263616), (15538969 / 18263616), (-428779 / 1521968), (6418301 / 2282952)]
theorem s0c2_psd : s0c2.PosSemidef := by
  apply psd_of_ldl s0c2 !![1, 0, 0, 0; (229694 / 17989595), 1, 0, 0; (2922663 / 14391676), (-78108664931135 / 1185719696310516), 1, 0; (-3595451 / 71958380), (93455204183183 / 395239898770172), (-286989721535858004312 / 3373603196364758426129), 1] ![(17989595 / 4565904), (98809974692543 / 27379587922960), (3373603196364758426129 / 1546823515503705784704), (45489112011586000418819650505 / 17604055232793869665024120704)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s0c2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s0c3 : Mat := !![(409123227 / 97405952), (1939085 / 97405952), (204051955 / 194811904), (-554187 / 1820672); (1939085 / 97405952), (372742345 / 97405952), (-68898139 / 194811904), (233569039 / 194811904); (204051955 / 194811904), (-68898139 / 194811904), (113627741 / 55660544), (-155148145 / 389623808); (-554187 / 1820672), (233569039 / 194811904), (-155148145 / 389623808), (1069647617 / 389623808)]
theorem s0c3_psd : s0c3.PosSemidef := by
  apply psd_of_ldl s0c3 !![1, 0, 0, 0; (1939085 / 409123227), 1, 0, 0; (204051955 / 818246454), (-7145875761783932 / 76246895487655045), 1, 0; (-19766003 / 272748818), (47836751421375309 / 152493790975310090), (-869478907927257189018 / 7238847365197712429383), 1] ![(409123227 / 97405952), (76246895487655045 / 19925518705623552), (7238847365197712429383 / 4144476251126977626020), (913459241185515195490688261 / 393474787382686856811542348)]
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
theorem identity0 (t : ℝ) : residual (0 + ((1 / 4) - 0) * t) = combination 3 coeff0 t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [residual, combination, weight, bernsteinPolynomial, Nat.choose, Finset.sum_range_succ, coeff0, s0c0, s0c1, s0c2, s0c3] <;> ring
theorem interval0 {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 4)) : (residual h).PosSemidef := by
  exact interval_psd 3 coeff0 residual (by norm_num) coeff0_psd identity0 hlo hhi
def s1c0 : Mat := !![(409123227 / 97405952), (1939085 / 97405952), (204051955 / 194811904), (-554187 / 1820672); (1939085 / 97405952), (372742345 / 97405952), (-68898139 / 194811904), (233569039 / 194811904); (204051955 / 194811904), (-68898139 / 194811904), (113627741 / 55660544), (-155148145 / 389623808); (-554187 / 1820672), (233569039 / 194811904), (-155148145 / 389623808), (1069647617 / 389623808)]
theorem s1c0_psd : s1c0.PosSemidef := by
  apply psd_of_ldl s1c0 !![1, 0, 0, 0; (1939085 / 409123227), 1, 0, 0; (204051955 / 818246454), (-7145875761783932 / 76246895487655045), 1, 0; (-19766003 / 272748818), (47836751421375309 / 152493790975310090), (-869478907927257189018 / 7238847365197712429383), 1] ![(409123227 / 97405952), (76246895487655045 / 19925518705623552), (7238847365197712429383 / 4144476251126977626020), (913459241185515195490688261 / 393474787382686856811542348)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s1c0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s1c1 : Mat := !![(651702641 / 146108928), (-1532953 / 146108928), (18016325 / 13915136), (-120366811 / 292217856); (-1532953 / 146108928), (590841851 / 146108928), (-1310371 / 2731008), (452083613 / 292217856); (18016325 / 13915136), (-1310371 / 2731008), (1007417249 / 584435712), (-100264433 / 194811904); (-120366811 / 292217856), (452083613 / 292217856), (-100264433 / 194811904), (14634185 / 5462016)]
theorem s1c1_psd : s1c1.PosSemidef := by
  apply psd_of_ldl s1c1 !![1, 0, 0, 0; (-1532953 / 651702641), 1, 0, 0; (378342825 / 1303405282), (-22698762015024388 / 192525422382564141), 1, 0; (-120366811 / 1303405282), (49073261313483175 / 128350281588376094), (-13362930054736749932727 / 81105688426116304209761), 1] ![(651702641 / 146108928), (64175140794188047 / 15869929041879808), (81105688426116304209761 / 62789471154159938689176), (26650193566112322233922462959 / 13225742400269933494877306748)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s1c1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s1c2 : Mat := !![(110873275 / 24351488), (-2108819 / 24351488), (204500617 / 146108928), (-77850811 / 146108928); (-2108819 / 24351488), (306364795 / 73054464), (-91078049 / 146108928), (267029341 / 146108928); (204500617 / 146108928), (-91078049 / 146108928), (56209943 / 41745408), (-180517331 / 292217856); (-77850811 / 146108928), (267029341 / 146108928), (-180517331 / 292217856), (253210625 / 97405952)]
theorem s1c2_psd : s1c2.PosSemidef := by
  apply psd_of_ldl s1c2 !![1, 0, 0, 0; (-2108819 / 110873275), 1, 0, 0; (204500617 / 665239650), (-2416716696649788 / 16977163406814671), 1, 0; (-77850811 / 665239650), (14721122144179783 / 33954326813629342), (-1621480822020295542502 / 6904065868756998295387), 1] ![(110873275 / 24351488), (16977163406814671 / 4049893838524800), (6904065868756998295387 / 8305296247267364311884), (639230953497920740971819867 / 375277404362155399344055772)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s1c2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def s1c3 : Mat := !![(53513179 / 12175744), (-2854419 / 12175744), (30209747 / 24351488), (-16782009 / 24351488); (-2854419 / 12175744), (7391151 / 1739392), (-19766491 / 24351488), (6930681 / 3478784); (30209747 / 24351488), (-19766491 / 24351488), (35337611 / 48702976), (-34872177 / 48702976); (-16782009 / 24351488), (6930681 / 3478784), (-34872177 / 48702976), (16758967 / 6957568)]
theorem s1c3_psd : s1c3.PosSemidef := by
  apply psd_of_ldl s1c3 !![1, 0, 0, 0; (-2854419 / 53513179), 1, 0, 0; (30209747 / 107026358), (-242884123815724 / 1380260098762821), 1, 0; (-16782009 / 107026358), (424712754211087 / 920173399175214), (-13308136900130136756 / 18322081281829498253), 1] ![(53513179 / 12175744), (1380260098762821 / 325781384065088), (18322081281829498253 / 75025417928351898276), (1264072087610647002329365 / 995915050155124207040068)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [s1c3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def coeff1 (k : ℕ) : Mat :=
  match k with
  | 0 => s1c0
  | 1 => s1c1
  | 2 => s1c2
  | 3 => s1c3
  | _ => 0
theorem coeff1_psd (k : ℕ) (hk : k < 4) : (coeff1 k).PosSemidef := by
  interval_cases k
  · exact s1c0_psd
  · exact s1c1_psd
  · exact s1c2_psd
  · exact s1c3_psd
theorem identity1 (t : ℝ) : residual ((1 / 4) + ((1 / 2) - (1 / 4)) * t) = combination 3 coeff1 t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [residual, combination, weight, bernsteinPolynomial, Nat.choose, Finset.sum_range_succ, coeff1, s1c0, s1c1, s1c2, s1c3] <;> ring
theorem interval1 {h : ℝ} (hlo : (1 / 4) ≤ h) (hhi : h ≤ (1 / 2)) : (residual h).PosSemidef := by
  exact interval_psd 3 coeff1 residual (by norm_num) coeff1_psd identity1 hlo hhi
theorem residual_psd {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 2)) : (residual h).PosSemidef := by
  by_cases hs0 : h ≤ (1 / 4)
  · exact interval0 (by linarith) hs0
  exact interval1 (by linarith) hhi
theorem residual_identity (h : ℝ) : P - (transition h).transpose * P * transition h - (h * 1) • (1 : Mat) = h • residual h := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P, transition, residual, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
theorem certified_decrease {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 2)) (x : Fin 4 → ℝ) :
    energy P (transition h *ᵥ x) ≤ energy P x - h * 1 * squaredNorm x := by
  apply step_decrease
  rw [residual_identity]
  exact (residual_psd hlo hhi).smul (by linarith)
theorem certified_contraction {h : ℝ} (hlo : 0 ≤ h) (hhi : h ≤ (1 / 2)) (x : Fin 4 → ℝ) :
    energy P (transition h *ᵥ x) ≤ (1 - h * 1 / upperBound) * energy P x := by
  apply contract_of_decrease P (transition h) (by linarith) (by norm_num) upper_pos upper_psd
  exact certified_decrease hlo hhi
theorem certified_jitter (h : ℕ → ℝ) (x : ℕ → Fin 4 → ℝ) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ (1 / 2))
    (hlo : ∀ k, hmin ≤ h k) (hhi : ∀ k, h k ≤ (1 / 2))
    (hdyn : ∀ k, x (k+1) = transition (h k) *ᵥ x k) (n : ℕ) :
    energy P (x n) ≤ (1 - hmin * 1 / upperBound) ^ n * energy P (x 0) := by
  apply jitter_energy P transition h x (by linarith) (by norm_num) upper_pos
    (by dsimp [upperBound]; nlinarith) P_psd upper_psd
    (fun t ht htmax => certified_decrease (by linarith) htmax) hlo hhi hdyn n
end LeanControls.Generated.CoupledPlanar
