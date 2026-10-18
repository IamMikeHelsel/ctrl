import WeightedProfiles

set_option maxHeartbeats 3000000
namespace Erdos128.FiniteProfileBridge
noncomputable section

def meanDegree (y j : ℚ) : ℚ := 2 * j / y
def lowCenter (y j R : ℚ) : ℚ :=
  j - 4 * R * (y - meanDegree y j) ^ 2 - meanDegree y j ^ 2
def baseSlope (y j R : ℚ) : ℚ :=
  8 * R * (y - meanDegree y j) - 2 * meanDegree y j
def lowCertificate (y j R L : ℚ) : ℚ :=
  lowCenter y j R + (L - baseSlope y j R) ^ 2 / (4 * (4 * R + 1))
def highCertificate (y j R L : ℚ) : ℚ :=
  ((j - R) / (y - 1 / 2) - L) ^ 2 / 4 + L * meanDegree y j

theorem low_square_identity (y j R L d : ℚ) (hK : 4 * R + 1 ≠ 0) :
    j - 4 * R * (y - d) ^ 2 - d ^ 2 - L * (d - meanDegree y j) =
      lowCertificate y j R L - (4 * R + 1) *
        (d - meanDegree y j - (baseSlope y j R - L) / (2 * (4 * R + 1))) ^ 2 := by
  unfold lowCertificate lowCenter baseSlope
  field_simp [hK]
  ring

theorem high_square_identity (y j R L d : ℚ) :
    d * (j - R) / (y - 1 / 2) - d ^ 2 - L * (d - meanDegree y j) =
      highCertificate y j R L - (d - ((j - R) / (y - 1 / 2) - L) / 2) ^ 2 := by
  unfold highCertificate
  ring

theorem low_majorant (y j R L : ℚ) (hR : 0 ≤ R)
    (hA : lowCertificate y j R L ≤ 0) (d : ℚ) :
    j - 4 * R * (y - d) ^ 2 - d ^ 2 ≤ L * (d - meanDegree y j) := by
  have hK : 0 < 4 * R + 1 := by linarith
  have hi := low_square_identity y j R L d hK.ne'
  have hs := mul_nonneg hK.le
    (sq_nonneg (d - meanDegree y j - (baseSlope y j R - L) / (2 * (4 * R + 1))))
  linarith

theorem high_majorant (y j R L : ℚ)
    (hH : highCertificate y j R L ≤ 0) (d : ℚ) :
    d * (j - R) / (y - 1 / 2) - d ^ 2 ≤ L * (d - meanDegree y j) := by
  have hi := high_square_identity y j R L d
  have hs := sq_nonneg (d - ((j - R) / (y - 1 / 2) - L) / 2)
  linarith

theorem low_scale_identity (y j R L d : ℚ) (hy : y ≠ 0) :
    y ^ 2 * (j / y ^ 2 - ((R / y ^ 2) / (1 / (2 * y)) ^ 2) * (1 - d) ^ 2 - d ^ 2 -
      (L / y) * (d - 2 * (j / y ^ 2))) =
      j - 4 * R * (y - y * d) ^ 2 - (y * d) ^ 2 -
        L * (y * d - meanDegree y j) := by
  unfold meanDegree
  field_simp [hy]
  ring

theorem high_scale_identity (y j R L d : ℚ) (hy : y ≠ 0)
    (hb : y - 1 / 2 ≠ 0) :
    y ^ 2 * (d * (j / y ^ 2 - R / y ^ 2) / (1 - 1 / (2 * y)) - d ^ 2 -
      (L / y) * (d - 2 * (j / y ^ 2))) =
      (y * d) * (j - R) / (y - 1 / 2) - (y * d) ^ 2 -
        L * (y * d - meanDegree y j) := by
  have ht : 2 * y - 1 ≠ 0 := by intro h; apply hb; linarith
  unfold meanDegree
  field_simp [hy, hb, ht]

theorem alpha_domain (y : ℚ) (hy : 1 / 2 < y) :
    0 < 1 / (2 * y) ∧ 1 / (2 * y) < 1 := by
  have hz : 0 < 2 * y := by linarith
  constructor
  · exact div_pos (by norm_num) hz
  · exact (div_lt_one hz).mpr (by linarith)

theorem normalized_certificates (y j R L : ℚ) (hy : 1 / 2 < y) (hR : 0 ≤ R)
    (hA : lowCertificate y j R L ≤ 0) (hH : highCertificate y j R L ≤ 0) :
    (∀ d : ℚ, j / y ^ 2 - ((R / y ^ 2) / (1 / (2 * y)) ^ 2) * (1 - d) ^ 2 - d ^ 2 ≤
      (L / y) * (d - 2 * (j / y ^ 2))) ∧
    (∀ d : ℚ, d * (j / y ^ 2 - R / y ^ 2) / (1 - 1 / (2 * y)) - d ^ 2 ≤
      (L / y) * (d - 2 * (j / y ^ 2))) := by
  have hy0 : 0 < y := by linarith
  have hb : y - 1 / 2 ≠ 0 := by linarith
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy0
  constructor
  · intro d
    have hm := low_majorant y j R L hR hA (y * d)
    have hs := low_scale_identity y j R L d hy0.ne'
    have hz : y ^ 2 * (j / y ^ 2 - ((R / y ^ 2) / (1 / (2 * y)) ^ 2) * (1 - d) ^ 2 - d ^ 2 -
        (L / y) * (d - 2 * (j / y ^ 2))) ≤ 0 := by linarith
    have := (mul_le_mul_iff_right₀ hy2).mp (show _ ≤ y ^ 2 * 0 by simpa using hz)
    linarith
  · intro d
    have hm := high_majorant y j R L hH (y * d)
    have hs := high_scale_identity y j R L d hy0.ne' hb
    have hz : y ^ 2 * (d * (j / y ^ 2 - R / y ^ 2) / (1 - 1 / (2 * y)) - d ^ 2 -
        (L / y) * (d - 2 * (j / y ^ 2))) ≤ 0 := by linarith
    have := (mul_le_mul_iff_right₀ hy2).mp (show _ ≤ y ^ 2 * 0 by simpa using hz)
    linarith

end
end Erdos128.FiniteProfileBridge
