module

public import LeanControls.RobustPD
public import Mathlib.Algebra.Order.Group.MinMax

/-! Exact scalar hard-clamp sector semantics. The sector bound permits active
clipping; it does not replace clipping by an assumed linear feedback law. -/

@[expose] public section
noncomputable section
namespace LeanControls.SaturationSector
open RobustPD

/-- A nonnegative symmetric actuator limit bounds the actual applied command. -/
theorem clamp_abs_le {U : ℝ} (hU : 0 ≤ U) (u : ℝ) : |saturate U u| ≤ U := by
  apply abs_le.mpr
  unfold saturate
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Division-free sector representation, including zero requests and both
clipping boundaries. Strict positivity of kappa gives a positive feedback gain. -/
theorem exists_sector_gain {U kappa u : ℝ}
    (hU : 0 < U) (_hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hbudget : kappa * |u| ≤ U) :
    ∃ alpha : ℝ, kappa ≤ alpha ∧ alpha ≤ 1 ∧ saturate U u = alpha * u := by
  by_cases hu : |u| ≤ U
  · refine ⟨1, hk1, le_rfl, ?_⟩
    rw [saturate_eq hu, one_mul]
  · have hab : U < |u| := lt_of_not_ge hu
    have hab0 : 0 < |u| := hU.trans hab
    refine ⟨U / |u|, (le_div_iff₀ hab0).mpr hbudget,
      (div_le_one hab0).mpr hab.le, ?_⟩
    rcases le_total 0 u with hpos | hneg
    · rw [abs_of_nonneg hpos] at hab ⊢
      have hu0 : u ≠ 0 := ne_of_gt (hU.trans hab)
      rw [saturate, min_eq_left hab.le, max_eq_right (by linarith : -U ≤ U)]
      field_simp
    · rw [abs_of_nonpos hneg] at hab ⊢
      have hu0 : u ≠ 0 := by linarith
      rw [saturate, min_eq_right (by linarith : u ≤ U), max_eq_left (by linarith : u ≤ -U)]
      field_simp

/-- Equivalent request-bound notation when division by kappa is convenient. -/
theorem exists_sector_gain_of_div {U kappa u : ℝ}
    (hU : 0 < U) (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hbudget : |u| ≤ U / kappa) :
    ∃ alpha : ℝ, kappa ≤ alpha ∧ alpha ≤ 1 ∧ saturate U u = alpha * u := by
  apply exists_sector_gain hU hk hk1
  have hh := (le_div_iff₀ hk).mp hbudget
  nlinarith only [hh]

/-- The division-free sector condition is also necessary for a gain in [kappa,1]. -/
theorem sector_budget_necessary {U kappa u alpha : ℝ}
    (hU : 0 ≤ U) (hk : 0 < kappa) (hka : kappa ≤ alpha)
    (hrep : saturate U u = alpha * u) : kappa * |u| ≤ U := by
  have ha : 0 ≤ alpha := hk.le.trans hka
  have hb := clamp_abs_le hU u
  rw [hrep, abs_mul, abs_of_nonneg ha] at hb
  exact (mul_le_mul_of_nonneg_right hka (abs_nonneg u)).trans hb

/-- Scalar clipping is nonexpansive even when either or both requests clip. -/
theorem clamp_nonexpansive (U u v : ℝ) :
    |saturate U u - saturate U v| ≤ |u - v| := by
  have hmax := abs_max_sub_max_le_max (-U) (min U u) (-U) (min U v)
  have hmin := abs_min_sub_min_le_max U u U v
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (min U u - min U v))] at hmax
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (u - v))] at hmin
  exact hmax.trans hmin

/-- Perturbing the request by e changes the applied command by at most |e|. -/
theorem clamp_perturbation (U u e : ℝ) :
    |saturate U (u + e) - saturate U u| ≤ |e| := by
  simpa using clamp_nonexpansive U (u + e) u

/-- A noisy clipped request is a sector-scaled nominal request plus a bounded
additive error. No assumption that clipping is inactive is used. -/
theorem sector_with_request_error {U kappa u : ℝ}
    (hU : 0 < U) (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hbudget : kappa * |u| ≤ U) (e : ℝ) :
    ∃ alpha d : ℝ, kappa ≤ alpha ∧ alpha ≤ 1 ∧ |d| ≤ |e| ∧
      saturate U (u + e) = alpha * u + d := by
  obtain ⟨alpha, ha0, ha1, ha⟩ := exists_sector_gain hU hk hk1 hbudget
  refine ⟨alpha, saturate U (u + e) - saturate U u, ha0, ha1,
    clamp_perturbation U u e, ?_⟩
  rw [ha]
  ring

/-- A boundary witness with genuine active clipping whenever kappa<1. -/
theorem active_sector_boundary {U kappa : ℝ} (hU : 0 < U)
    (hk : 0 < kappa) (hk1 : kappa < 1) :
    U < U / kappa ∧ kappa * |U / kappa| = U ∧
      saturate U (U / kappa) = kappa * (U / kappa) := by
  have hup : 0 < U / kappa := div_pos hU hk
  have hlarge : U < U / kappa := (lt_div_iff₀ hk).mpr (by nlinarith)
  have hcancel : kappa * (U / kappa) = U := by field_simp
  refine ⟨hlarge, ?_, ?_⟩
  · rw [abs_of_pos hup, hcancel]
  · rw [hcancel, saturate, min_eq_left hlarge.le,
      max_eq_right (by linarith : -U ≤ U)]

end LeanControls.SaturationSector
