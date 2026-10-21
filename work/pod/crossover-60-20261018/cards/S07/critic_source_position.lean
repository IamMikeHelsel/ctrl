import LeanControls.TravelSafety
import Mathlib.Tactic
noncomputable section
namespace S07CriticPosition
open LeanControls Matrix
/-- Sharp position support bound binds the literal source energy/P, not a renamed quadratic. -/
theorem sharp_position (z : SaturatedLag.State) :
    (z 0)^2 ≤ (3550075/11131832:ℝ)*TravelSafety.V z := by
  have he : (3550075/11131832:ℝ)*TravelSafety.V z-(z 0)^2 =
    (7924369/5565916:ℝ)*(z 0+(36494771/15848738:ℝ)*z 1+(17750375/15848738:ℝ)*z 2)^2+
    (38095377836923/44106372207004:ℝ)*(z 1+(46767/32758:ℝ)*z 2)^2 := by
    simp [TravelSafety.V, BernsteinCertificate.energy, TravelSafety.P,
      Generated.TravelQuarterLower.P, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  have h0 : 0≤(7924369/5565916:ℝ)*(z 0+(36494771/15848738:ℝ)*z 1+(17750375/15848738:ℝ)*z 2)^2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0≤(38095377836923/44106372207004:ℝ)*(z 1+(46767/32758:ℝ)*z 2)^2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  linarith

theorem core_position {z : SaturatedLag.State} (hz : TravelSafety.V z≤11) : |z 0|≤15/8 := by
  have hp := sharp_position z
  have hbudget : (3550075/11131832:ℝ)*11≤(15/8)^2 := by norm_num
  have hbound : (z 0)^2≤(15/8:ℝ)^2 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (z 0-15/8),sq_nonneg (z 0+15/8)]
theorem core_position_twelve {z : SaturatedLag.State} (hz : TravelSafety.V z≤12) : |z 0|≤49/25 := by
  have hp := sharp_position z
  have hbudget : (3550075/11131832:ℝ)*12≤(49/25)^2 := by norm_num
  have hbound : (z 0)^2≤(49/25:ℝ)^2 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (z 0-49/25),sq_nonneg (z 0+49/25)]
end S07CriticPosition
#print axioms S07CriticPosition.sharp_position
#print axioms S07CriticPosition.core_position

#print axioms S07CriticPosition.core_position_twelve
