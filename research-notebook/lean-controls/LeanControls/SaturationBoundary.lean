module

public import LeanControls.Certificate

@[expose] public section
noncomputable section
namespace LeanControls.SaturationBoundary

/-- The current conservative budget actually excludes active rounding-induced
clipping, even though the one-step clipping bound permits it abstractly. -/
theorem budget_forces_clipping_inactive
    {theta hmin delta U R W x v : ℝ}
    (ht : 0 < theta) (hd : 0 < delta) (hW : 0 ≤ W) (hU : 0 ≤ U)
    (hR : 10 * R ≤ U ^ 2) (hminhi : hmin ≤ 1 / 2)
    (hE : PD.energy x v ≤ R)
    (hbudget : Certificate.multiplier theta hmin * R +
      Certificate.disturbanceBudget theta delta W ≤ R) :
    |SampledPD.control (Quantized.quantize delta x) (Quantized.quantize delta v)| < U := by
  let D := 5 * delta / 2 + W
  let q := Certificate.multiplier theta hmin
  let b := Certificate.disturbanceBudget theta delta W
  have hD : 0 < D := by dsimp [D]; positivity
  have hb : 0 < b := by dsimp [b, Certificate.disturbanceBudget]; positivity
  have hq : (11 / 12) * (1 + theta) ≤ q := by
    dsimp [q, Certificate.multiplier]
    nlinarith [mul_nonneg ht.le (show 0 ≤ 1 / 2 - hmin by linarith)]
  have hR0 : 0 ≤ R := (PD.energy_nonneg _ _).trans hE
  have hbudget' : q * R + b ≤ R := hbudget
  have hRpos : 0 < R := by
    by_contra hn
    have hr : R = 0 := le_antisymm (by linarith) hR0
    rw [hr] at hbudget'
    nlinarith
  have hq1 : q < 1 := by nlinarith
  have htmax : theta ≤ 1 / 11 := by linarith
  have hi : 11 ≤ theta⁻¹ := by
    have hh := one_div_le_one_div_of_le ht htmax
    norm_num [one_div] at hh
    exact hh
  have hbD : 25 * D ^ 2 ≤ b := by
    have hh := mul_nonneg (show 0 ≤ theta⁻¹ - 11 by linarith) (sq_nonneg D)
    dsimp [b, Certificate.disturbanceBudget, D] at *
    nlinarith only [hh, sq_nonneg (5 * delta / 2 + W)]
  have hqR : (11 / 12) * R ≤ q * R :=
    mul_le_mul_of_nonneg_right (by linarith) hR0
  have hD2 : D ^ 2 ≤ R / 300 := by nlinarith only [hbD, hqR, hbudget']
  let u := SampledPD.control x v
  let e := SampledPD.control (Quantized.quantize delta x) (Quantized.quantize delta v) - u
  have he : |e| ≤ D := by
    exact (Quantized.quantized_control_error hd x v).trans (by dsimp [D]; linarith)
  have he2 : e ^ 2 ≤ D ^ 2 := by nlinarith [abs_le.mp he]
  have hu2 : u ^ 2 ≤ (37 / 4) * PD.energy x v := by
    dsimp [u, SampledPD.control, PD.energy]
    nlinarith [sq_nonneg (13 * x + v)]
  have hsum : (u + e) ^ 2 ≤ (21 / 20) * u ^ 2 + 21 * e ^ 2 := by
    nlinarith [sq_nonneg (u - 20 * e)]
  have hsumU : (u + e) ^ 2 < U ^ 2 := by
    nlinarith only [hsum, hu2, he2, hD2, hR, hE, hRpos]
  have hsumEq : u + e = SampledPD.control (Quantized.quantize delta x) (Quantized.quantize delta v) := by
    dsimp [e]; ring
  rw [hsumEq] at hsumU
  exact abs_lt_of_sq_lt_sq hsumU hU

end LeanControls.SaturationBoundary
