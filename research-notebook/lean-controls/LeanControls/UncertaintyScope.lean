module
public import LeanControls.UncertainTravel

/-! Exact ablations for the uncertainty extension. The broad-sector obstruction
concerns the fixed common quadratic certificate, not the safety of the actual
clipped controller. The response comparisons concern a sufficient error budget.
-/
@[expose] public section
noncomputable section
namespace LeanControls.UncertaintyScope
open Matrix BernsteinCertificate
abbrev P := Generated.TravelQuarterLower.P
abbrev State := UncertainLag.State

/-- Infinitesimal plant with a sector gain held constant. -/
def generator (r alpha : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 0, 0, 1; -r*alpha, -3*r*alpha, -r*(1+2*alpha)]

/-- Negative derivative matrix for the candidate common energy. -/
def dissipation (r alpha : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  -(P * generator r alpha + (generator r alpha).transpose * P)

theorem generator_matches_vectorField (r alpha : ℝ) (z : State) :
    generator r alpha *ᵥ z =
      UncertainLag.vectorField r (alpha * SaturatedLag.input z) z := by
  ext i
  fin_cases i <;>
    simp [generator, UncertainLag.vectorField, SaturatedLag.input,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

def obstruction : State := ![-1529/2000,-9/4,0]

theorem broad_sector_negative :
    energy (dissipation (9/10) (1/4)) obstruction = -4597569/16000000 := by
  norm_num [energy, dissipation, generator, P, Generated.TravelQuarterLower.P,
    obstruction, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]

theorem broad_sector_not_psd : ¬ (dissipation (9/10) (1/4)).PosSemidef := by
  intro h
  have h0 := h.dotProduct_mulVec_nonneg obstruction
  change 0 ≤ energy (dissipation (9/10) (1/4)) obstruction at h0
  rw [broad_sector_negative] at h0
  norm_num at h0

/-- Even a zero nonnegative common decay margin is impossible at this admitted
broad-sector endpoint for the fixed P. This does not refute another P or method. -/
theorem broad_sector_no_nonnegative_margin :
    ¬ ∃ c : ℝ, 0 ≤ c ∧ ∀ z : State,
      c * squaredNorm z ≤ energy (dissipation (9/10) (1/4)) z := by
  rintro ⟨c, hc, h⟩
  have hn : 0 ≤ squaredNorm obstruction := by
    unfold squaredNorm
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb := h obstruction
  rw [broad_sector_negative] at hb
  nlinarith [mul_nonneg hc hn]

/-- Coarse trace-times-norm response estimate fails the SAME sufficient budget. -/
theorem uncertain_coarse_budget_fails :
    (12 : ℝ) * (15/902) < (27511/500) * (1/5 + 1/(15/902)) * (1/100)^2 := by
  norm_num

theorem uncertain_direct_budget_passes :
    (16 : ℝ) * (1/5 + 1/(15/902)) * (1/100)^2 < 12 * (15/902) := by
  norm_num

theorem uncertain_larger_budget_passes :
    (16 : ℝ) * (1/5 + 1/(15/902)) * (1/90)^2 < 12 * (15/902) := by
  norm_num

end LeanControls.UncertaintyScope
