module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

noncomputable section

theorem unit_normal_exists (p q : ℝ) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ p * s - q * c = 0 := by
  by_cases hpq : p ^ 2 + q ^ 2 = 0
  · refine ⟨1, 0, by norm_num, ?_⟩
    have hp : p = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hq : q = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    simp [hp, hq]
  · have hpos : 0 < p ^ 2 + q ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hpq)
    let r := Real.sqrt (p ^ 2 + q ^ 2)
    have hr2 : r ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt (le_of_lt hpos)
    have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    refine ⟨p / r, q / r, ?_, ?_⟩
    · calc
        (p / r) ^ 2 + (q / r) ^ 2 = (p ^ 2 + q ^ 2) / r ^ 2 := by ring
        _ = r ^ 2 / r ^ 2 := by rw [hr2]
        _ = 1 := div_self (pow_ne_zero 2 hr0)
    · ring

theorem half_angle_exists (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧ x ^ 2 - y ^ 2 = c ∧ 2 * x * y = s := by
  by_cases hc : c = -1
  · refine ⟨0, 1, by norm_num, by linarith, ?_⟩
    have hs2 : s ^ 2 = 0 := by
      rw [hc] at hcs
      linarith
    have hs : s = 0 := sq_eq_zero_iff.mp hs2
    linarith
  · have h1c_nonneg : 0 ≤ 1 + c := by
      have h2 : 0 ≤ (1 + c) ^ 2 + s ^ 2 := by positivity
      have h3 : (1 + c) ^ 2 + s ^ 2 = 2 * (1 + c) := by linear_combination hcs
      linarith
    have h1c_pos : 0 < 1 + c := lt_of_le_of_ne h1c_nonneg (by intro h; apply hc; linarith)
    have hx2_nonneg : 0 ≤ (1 + c) / 2 := by linarith
    let x := Real.sqrt ((1 + c) / 2)
    have hx_sq : x ^ 2 = (1 + c) / 2 := Real.sq_sqrt hx2_nonneg
    have hx_pos : 0 < x := Real.sqrt_pos.mpr (by linarith)
    have hx_ne : 2 * x ≠ 0 := by linarith
    let y := s / (2 * x)
    have hy_mul : 2 * x * y = s := mul_div_cancel₀ s hx_ne
    have hy_sq : y ^ 2 = (1 - c) / 2 := by
      have h4x2 : 4 * x ^ 2 * y ^ 2 = s ^ 2 := by
        calc
          4 * x ^ 2 * y ^ 2 = (2 * x * y) ^ 2 := by ring
          _ = s ^ 2 := by rw [hy_mul]
      rw [hx_sq] at h4x2
      have h_eq : (1 + c) * (2 * y ^ 2 - (1 - c)) = 0 := by
        linear_combination h4x2 + hcs
      cases mul_eq_zero.mp h_eq with
      | inl h_zero => exfalso; linarith
      | inr h_y => linarith
    refine ⟨x, y, by linarith, by linarith, hy_mul⟩

theorem signed_svd_angles_exist (b00 b01 b10 b11 : ℝ) :
    ∃ cu su cv sv : ℝ,
      cu ^ 2 + su ^ 2 = 1 ∧
      cv ^ 2 + sv ^ 2 = 1 ∧
      -cu * sv * b00 + cu * cv * b01 - su * sv * b10 + su * cv * b11 = 0 ∧
      -su * cv * b00 - su * sv * b01 + cu * cv * b10 + cu * sv * b11 = 0 := by
  obtain ⟨cp, sp, hcp, heqp⟩ := unit_normal_exists (b00 - b11) (b01 + b10)
  obtain ⟨cm, sm, hcm, heqm⟩ := unit_normal_exists (b00 + b11) (b01 - b10)
  have h2cs : (cp * cm + sp * sm) ^ 2 + (sp * cm - cp * sm) ^ 2 = 1 := by
    calc
      (cp * cm + sp * sm) ^ 2 + (sp * cm - cp * sm) ^ 2 =
          (cp ^ 2 + sp ^ 2) * (cm ^ 2 + sm ^ 2) := by ring
      _ = 1 * 1 := by rw [hcp, hcm]
      _ = 1 := by ring
  obtain ⟨x, y, hxy, hcos2, hsin2⟩ :=
    half_angle_exists (cp * cm + sp * sm) (sp * cm - cp * sm) h2cs
  let cu := x
  let su := y
  let cv := x * cm - y * sm
  let sv := x * sm + y * cm
  have hcv : cv ^ 2 + sv ^ 2 = 1 := by
    dsimp [cv, sv]
    calc
      (x * cm - y * sm) ^ 2 + (x * sm + y * cm) ^ 2 =
          (x ^ 2 + y ^ 2) * (cm ^ 2 + sm ^ 2) := by ring
      _ = 1 * 1 := by rw [hxy, hcm]
      _ = 1 := by ring
  have h_sum_c : cu * cv - su * sv = cp := by
    dsimp [cu, su, cv, sv]
    linear_combination cm * hcos2 - sm * hsin2 + cp * hcm
  have h_sum_s : su * cv + cu * sv = sp := by
    dsimp [cu, su, cv, sv]
    linear_combination sm * hcos2 + cm * hsin2 + sp * hcm
  have h_diff_c : cu * cv + su * sv = cm := by
    dsimp [cu, su, cv, sv]
    linear_combination cm * hxy
  have h_diff_s : su * cv - cu * sv = -sm := by
    dsimp [cu, su, cv, sv]
    linear_combination -sm * hxy
  refine ⟨cu, su, cv, sv, hxy, hcv, ?_, ?_⟩
  · have h1 : -cu * sv * b00 + cu * cv * b01 - su * sv * b10 + su * cv * b11 =
        (1/2) * ((b01 + b10) * (cu * cv - su * sv) - (b00 - b11) * (su * cv + cu * sv)) +
        (1/2) * ((b01 - b10) * (cu * cv + su * sv) + (b00 + b11) * (su * cv - cu * sv)) := by ring
    rw [h1, h_sum_c, h_sum_s, h_diff_c, h_diff_s]
    linear_combination -(1/2) * heqp - (1/2) * heqm
  · have h2 : -su * cv * b00 - su * sv * b01 + cu * cv * b10 + cu * sv * b11 =
        (1/2) * ((b01 + b10) * (cu * cv - su * sv) - (b00 - b11) * (su * cv + cu * sv)) -
        (1/2) * ((b01 - b10) * (cu * cv + su * sv) + (b00 + b11) * (su * cv - cu * sv)) := by ring
    rw [h2, h_sum_c, h_sum_s, h_diff_c, h_diff_s]
    linear_combination -(1/2) * heqp + (1/2) * heqm

#print axioms signed_svd_angles_exist
