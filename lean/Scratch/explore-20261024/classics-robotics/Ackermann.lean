import Mathlib

/-!
# Ackermann steering (Lankensperger 1816 / Ackermann 1818) and the kinematic bicycle model

Car body frame: rear axle on the `x = 0` line, front axle on `x = L`, wheels at `y = ±w/2`.
A planar rigid-body velocity field with velocity `(v, vy)` at the rear-axle centre and yaw
rate `ω` gives velocity `(v - ω y, vy + ω x)` at body point `(x, y)`.
A wheel at `(x, y)` with heading `δ` does not slip laterally iff the velocity there is parallel
to `(cos δ, sin δ)`, i.e. `cos δ * uy - sin δ * ux = 0`.
-/

namespace Classics.Ackermann

open Real

/-- Velocity at body point `(x, y)` of the rigid motion `(v, vy, ω)`. -/
def vel (v vy ω x y : ℝ) : ℝ × ℝ := (v - ω * y, vy + ω * x)

/-- No lateral slip of a wheel at `(x,y)` with heading `δ`. -/
def NoSlip (v vy ω x y δ : ℝ) : Prop :=
  cos δ * (vel v vy ω x y).2 - sin δ * (vel v vy ω x y).1 = 0

/-- Unsteered rear wheels force zero lateral velocity at the rear axle. -/
theorem noSlip_rear_iff (v vy ω y : ℝ) : NoSlip v vy ω 0 y 0 ↔ vy = 0 := by
  simp [NoSlip, vel]

/-- A front wheel at `(L, y)` with `sin δ ≠ 0`: no slip iff `L cot δ = R - y` where `R = v/ω`
is the turning radius (the wheel axis passes through the ICR `(0, R)`). -/
theorem noSlip_front_iff {v ω L y δ : ℝ} (hω : ω ≠ 0) (hs : sin δ ≠ 0) :
    NoSlip v 0 ω L y δ ↔ L * cot δ = v / ω - y := by
  rw [NoSlip, vel, cot_eq_cos_div_sin]
  constructor
  · intro h; field_simp; linear_combination h
  · intro h; field_simp at h; linear_combination h

/-- **Ackermann condition.** If the rear axle doesn't slip and both front wheels
(inner at `y = w/2`, outer at `y = -w/2`, turning left with `ω ≠ 0`) don't slip, then
`cot δ_o - cot δ_i = w / L`. -/
theorem ackermann {v vy ω L w δi δo : ℝ} (hω : ω ≠ 0) (hL : L ≠ 0)
    (hi : sin δi ≠ 0) (ho : sin δo ≠ 0)
    (hrl : NoSlip v vy ω 0 (w / 2) 0) (hrr : NoSlip v vy ω 0 (-w / 2) 0)
    (hfi : NoSlip v vy ω L (w / 2) δi) (hfo : NoSlip v vy ω L (-w / 2) δo) :
    cot δo - cot δi = w / L := by
  have hvy := (noSlip_rear_iff _ _ _ _).1 hrl
  subst hvy
  have h1 := (noSlip_front_iff hω hi).1 hfi
  have h2 := (noSlip_front_iff hω ho).1 hfo
  field_simp
  linear_combination h2 - h1

/-- **Converse.** If `cot δ_o - cot δ_i = w/L`, there is a genuinely turning rigid motion
(any forward speed `v ≠ 0`) under which all four wheels roll without slip. -/
theorem ackermann_converse {v L w δi δo : ℝ} (hv : v ≠ 0) (hL : L ≠ 0)
    (hi : sin δi ≠ 0) (ho : sin δo ≠ 0) (hδ : cot δo - cot δi = w / L)
    (hR : L * cot δi + w / 2 ≠ 0) :
    ∃ ω ≠ 0, NoSlip v 0 ω 0 (w / 2) 0 ∧ NoSlip v 0 ω 0 (-w / 2) 0 ∧
      NoSlip v 0 ω L (w / 2) δi ∧ NoSlip v 0 ω L (-w / 2) δo := by
  set R := L * cot δi + w / 2 with hRdef
  refine ⟨v / R, div_ne_zero hv hR, by simp [NoSlip, vel], by simp [NoSlip, vel], ?_, ?_⟩
  · rw [noSlip_front_iff (div_ne_zero hv hR) hi]; field_simp; ring
  · rw [noSlip_front_iff (div_ne_zero hv hR) ho]
    have : cot δo = cot δi + w / L := by linarith
    rw [this]; field_simp; ring

/-- **Kinematic bicycle model.** A virtual centre front wheel at `(L, 0)` with steering angle `δ`
(`cos δ ≠ 0`) rolls without slip iff the yaw rate is `ω = v tan δ / L`. -/
theorem bicycle_yaw_rate {v ω L δ : ℝ} (hL : L ≠ 0) (hc : cos δ ≠ 0) :
    NoSlip v 0 ω L 0 δ ↔ ω = v * tan δ / L := by
  rw [NoSlip, vel, tan_eq_sin_div_cos]
  constructor
  · intro h; field_simp; linear_combination h
  · intro h; rw [h]; field_simp; ring

/-- **Bicycle ↔ Ackermann consistency.** Under a no-slip turning motion, the bicycle-model
steering angle `δ` of the virtual centre wheel is the *cotangent average* of the inner and outer
Ackermann angles: `cot δ = (cot δ_i + cot δ_o)/2`. (Not the arithmetic mean of the angles!) -/
theorem bicycle_cot_average {v ω L w δ δi δo : ℝ} (hω : ω ≠ 0) (hL : L ≠ 0)
    (hs : sin δ ≠ 0) (hi : sin δi ≠ 0) (ho : sin δo ≠ 0)
    (h : NoSlip v 0 ω L 0 δ) (hfi : NoSlip v 0 ω L (w / 2) δi)
    (hfo : NoSlip v 0 ω L (-w / 2) δo) :
    cot δ = (cot δi + cot δo) / 2 := by
  have h0 := (noSlip_front_iff hω hs).1 h
  have h1 := (noSlip_front_iff hω hi).1 hfi
  have h2 := (noSlip_front_iff hω ho).1 hfo
  have : L * cot δ = L * ((cot δi + cot δo) / 2) := by linear_combination h0 - (h1 + h2) / 2
  exact mul_left_cancel₀ hL this

/-- Curvature of the bicycle path: `κ = ω / v = tan δ / L` (openpilot's
`curvature = tan(steer)/wheelbase` at zero slip). -/
theorem bicycle_curvature {v ω L δ : ℝ} (hv : v ≠ 0) (hL : L ≠ 0) (hc : cos δ ≠ 0)
    (h : NoSlip v 0 ω L 0 δ) : ω / v = tan δ / L := by
  rw [(bicycle_yaw_rate hL hc).1 h]; field_simp

/-- The inner wheel always steers more than the outer one: for a left turn with steering angles
in `(0, π/2)` and positive track/wheelbase, `δ_o < δ_i`. -/
theorem outer_lt_inner {L w δi δo : ℝ} (hL : 0 < L) (hw : 0 < w)
    (hi : δi ∈ Set.Ioo 0 (π / 2)) (ho : δo ∈ Set.Ioo 0 (π / 2))
    (hδ : cot δo - cot δi = w / L) : δo < δi := by
  have hpos : 0 < w / L := div_pos hw hL
  by_contra hle
  push Not at hle
  -- cot = cos/sin is antitone on (0, π/2)
  have hsi : 0 < sin δi := sin_pos_of_pos_of_lt_pi hi.1 (by linarith [hi.2, pi_pos])
  have hso : 0 < sin δo := sin_pos_of_pos_of_lt_pi ho.1 (by linarith [ho.2, pi_pos])
  have hsin : sin δi ≤ sin δo :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [hi.1, pi_pos]) ho.2.le hle
  have hcos : cos δo ≤ cos δi :=
    cos_le_cos_of_nonneg_of_le_pi hi.1.le (by linarith [ho.2, pi_pos]) hle
  have hci : 0 ≤ cos δi := cos_nonneg_of_mem_Icc ⟨by linarith [hi.1, pi_pos], hi.2.le⟩
  have hco : 0 ≤ cos δo := cos_nonneg_of_mem_Icc ⟨by linarith [ho.1, pi_pos], ho.2.le⟩
  have : cot δo ≤ cot δi := by
    rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, div_le_div_iff₀ hso hsi]
    nlinarith [mul_le_mul hcos hsin hsi.le hci]
  linarith

end Classics.Ackermann
