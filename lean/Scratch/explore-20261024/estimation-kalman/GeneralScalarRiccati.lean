import Mathlib

/-!
Scalar Kalman filter for `x_{k+1} = a x_k + w`, `z = x + v`, `Var w = q`, `Var v = r`.
Prior-to-prior Riccati map `ric a q r p = a² · p r / (p + r) + q`
(= `a² p - a² p² / (p + r) + q`).
-/

namespace ExploreKalman

noncomputable def ric (a q r p : ℝ) : ℝ := a ^ 2 * (p * r / (p + r)) + q

theorem ric_eq_textbook {a q r p : ℝ} (h : p + r ≠ 0) :
    ric a q r p = a ^ 2 * p - a ^ 2 * p ^ 2 / (p + r) + q := by
  unfold ric; field_simp; ring

/-- Key identity: `(p + r) (p - ric p)` is the DARE quadratic. -/
theorem dare_quad_eq {a q r p : ℝ} (h : p + r ≠ 0) :
    (p + r) * (p - ric a q r p) = p ^ 2 - (q + (a ^ 2 - 1) * r) * p - q * r := by
  unfold ric; field_simp; ring

/-- Closed-form steady state. -/
noncomputable def dareSS (a q r : ℝ) : ℝ :=
  (q + (a ^ 2 - 1) * r + Real.sqrt ((q + (a ^ 2 - 1) * r) ^ 2 + 4 * q * r)) / 2

noncomputable def dareSSneg (a q r : ℝ) : ℝ :=
  (q + (a ^ 2 - 1) * r - Real.sqrt ((q + (a ^ 2 - 1) * r) ^ 2 + 4 * q * r)) / 2

theorem quad_factor (a q r p : ℝ) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    p ^ 2 - (q + (a ^ 2 - 1) * r) * p - q * r = (p - dareSS a q r) * (p - dareSSneg a q r) := by
  unfold dareSS dareSSneg
  have := Real.sq_sqrt (show 0 ≤ (q + (a ^ 2 - 1) * r) ^ 2 + 4 * q * r by positivity)
  nlinarith

theorem dareSSneg_nonpos (a q r : ℝ) (hq : 0 ≤ q) (hr : 0 ≤ r) : dareSSneg a q r ≤ 0 := by
  unfold dareSSneg
  have : |q + (a ^ 2 - 1) * r| ≤ Real.sqrt ((q + (a ^ 2 - 1) * r) ^ 2 + 4 * q * r) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hq hr])
  linarith [le_abs_self (q + (a ^ 2 - 1) * r)]

theorem dareSS_pos (a : ℝ) {q r : ℝ} (hq : 0 < q) (hr : 0 < r) : 0 < dareSS a q r := by
  unfold dareSS
  have : |q + (a ^ 2 - 1) * r| < Real.sqrt ((q + (a ^ 2 - 1) * r) ^ 2 + 4 * q * r) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith [mul_pos hq hr])
  linarith [neg_abs_le (q + (a ^ 2 - 1) * r)]

/-- `dareSS` is a fixed point of the general scalar Riccati map. -/
theorem ric_dareSS (a : ℝ) {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    ric a q r (dareSS a q r) = dareSS a q r := by
  have hS := dareSS_pos a hq hr
  have hne : dareSS a q r + r ≠ 0 := by positivity
  have h := dare_quad_eq (a := a) (q := q) hne
  rw [quad_factor a q r _ hq.le hr.le, sub_self, zero_mul] at h
  have := (mul_eq_zero.1 h).resolve_left hne
  linarith

/-- **Uniqueness**: `dareSS` is the unique nonnegative fixed point (for `q > 0`). -/
theorem ric_fixed_unique (a : ℝ) {q r p : ℝ} (hq : 0 < q) (hr : 0 < r) (hp : 0 ≤ p)
    (h : ric a q r p = p) : p = dareSS a q r := by
  have hne : p + r ≠ 0 := by positivity
  have e := dare_quad_eq (a := a) (q := q) hne
  rw [h, sub_self, mul_zero, quad_factor a q r p hq.le hr.le] at e
  rcases mul_eq_zero.1 e.symm with h1 | h1
  · linarith
  · -- p = dareSSneg ≤ 0, but then p = 0 and the quadratic gives -q r = 0
    have hn := dareSSneg_nonpos a q r hq.le hr.le
    have hp0 : p = 0 := by linarith
    subst hp0
    unfold ric at h; simp at h; linarith

/-- Sub-solutions lie below the steady state: if `p ≤ ric p` then `p ≤ dareSS`. -/
theorem le_dareSS_of_le_ric (a : ℝ) {q r p : ℝ} (hq : 0 ≤ q) (hr : 0 < r) (hp : 0 ≤ p)
    (h : p ≤ ric a q r p) : p ≤ dareSS a q r := by
  have hne : 0 < p + r := by positivity
  have e := dare_quad_eq (a := a) (q := q) hne.ne'
  rw [quad_factor a q r p hq hr.le] at e
  have hn := dareSSneg_nonpos a q r hq hr.le
  by_contra hc
  push Not at hc
  have : 0 < (p - dareSS a q r) * (p - dareSSneg a q r) := by
    rcases eq_or_lt_of_le hn with hn0 | hn0
    · -- dareSSneg = 0 : need p > 0
      have : 0 < p - dareSSneg a q r := by
        have : dareSSneg a q r < p := by
          rcases eq_or_lt_of_le hp with h0 | h0
          · -- p = 0 < dareSS?  then hc says dareSS < 0
            exfalso
            have : 0 ≤ dareSS a q r := by
              unfold dareSS
              have : |q + (a ^ 2 - 1) * r| ≤
                  Real.sqrt ((q + (a ^ 2 - 1) * r) ^ 2 + 4 * q * r) := by
                rw [← Real.sqrt_sq_eq_abs]
                exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hq hr.le])
              linarith [neg_abs_le (q + (a ^ 2 - 1) * r)]
            linarith
          · linarith
        linarith
      exact mul_pos (by linarith) this
    · exact mul_pos (by linarith) (by linarith)
  nlinarith [mul_nonneg hne.le (sub_nonneg.2 h)]

/-- Monotonicity of the Riccati map in the prior variance. -/
theorem ric_mono_p (a q : ℝ) {r p p' : ℝ} (hr : 0 < r) (hp : 0 ≤ p) (hpp : p ≤ p') :
    ric a q r p ≤ ric a q r p' := by
  have hp' : 0 ≤ p' := hp.trans hpp
  have h : p * r / (p + r) ≤ p' * r / (p' + r) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hr.le hr.le]
  unfold ric
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg a)]

/-- Monotonicity of the Riccati map in the measurement noise `r`. -/
theorem ric_mono_r (a q : ℝ) {r r' p : ℝ} (hr : 0 < r) (hrr : r ≤ r') (hp : 0 ≤ p) :
    ric a q r p ≤ ric a q r' p := by
  have hr' : 0 < r' := hr.trans_le hrr
  have h : p * r / (p + r) ≤ p * r' / (p + r') := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hp hp) (sub_nonneg.2 hrr)]
  unfold ric
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg a)]

/-- **More sensor noise ⇒ larger steady-state variance.** -/
theorem dareSS_mono_r (a : ℝ) {q r r' : ℝ} (hq : 0 < q) (hr : 0 < r) (hrr : r ≤ r') :
    dareSS a q r ≤ dareSS a q r' := by
  have hS := dareSS_pos a hq hr
  apply le_dareSS_of_le_ric a hq.le (hr.trans_le hrr) hS.le
  calc dareSS a q r = ric a q r (dareSS a q r) := (ric_dareSS a hq hr).symm
    _ ≤ ric a q r' (dareSS a q r) := ric_mono_r a q hr hrr hS.le

/-- **More process noise ⇒ larger steady-state variance.** -/
theorem dareSS_mono_q (a : ℝ) {q q' r : ℝ} (hq : 0 < q) (hqq : q ≤ q') (hr : 0 < r) :
    dareSS a q r ≤ dareSS a q' r := by
  have hS := dareSS_pos a hq hr
  apply le_dareSS_of_le_ric a (hq.le.trans hqq) hr hS.le
  calc dareSS a q r = ric a q r (dareSS a q r) := (ric_dareSS a hq hr).symm
    _ ≤ ric a q' r (dareSS a q r) := by unfold ric; linarith

/-- **Larger |a| ⇒ larger steady-state variance.** -/
theorem dareSS_mono_a {a a' q r : ℝ} (hq : 0 < q) (hr : 0 < r) (haa : a ^ 2 ≤ a' ^ 2) :
    dareSS a q r ≤ dareSS a' q r := by
  have hS := dareSS_pos a hq hr
  apply le_dareSS_of_le_ric a' hq.le hr hS.le
  calc dareSS a q r = ric a q r (dareSS a q r) := (ric_dareSS a hq hr).symm
    _ ≤ ric a' q r (dareSS a q r) := by
        unfold ric; gcongr

/-- Sanity: the general closed form specialises to the project's random-walk steady state. -/
theorem dareSS_one (q r : ℝ) :
    dareSS 1 q r = (q + Real.sqrt (q ^ 2 + 4 * q * r)) / 2 := by
  unfold dareSS; norm_num

/-- `a = 0`: the filter forgets everything; steady state is `q`. -/
theorem ric_zero (q r p : ℝ) : ric 0 q r p = q := by unfold ric; simp

theorem dareSS_zero {q r : ℝ} (hq : 0 < q) (hr : 0 < r) : dareSS 0 q r = q :=
  (ric_fixed_unique 0 hq hr hq.le (ric_zero q r q)).symm

/-- **Stable `a`: global contraction** with factor `a²` on `[0, ∞)`. -/
theorem ric_lipschitz (a q : ℝ) {r p p' : ℝ} (hr : 0 < r) (hp : 0 ≤ p) (hp' : 0 ≤ p') :
    |ric a q r p - ric a q r p'| ≤ a ^ 2 * |p - p'| := by
  have e : ric a q r p - ric a q r p' =
      a ^ 2 * (r ^ 2 / ((p + r) * (p' + r))) * (p - p') := by
    unfold ric; field_simp; ring
  rw [e, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg a),
    abs_of_nonneg (by positivity : 0 ≤ r ^ 2 / ((p + r) * (p' + r)))]
  have : r ^ 2 / ((p + r) * (p' + r)) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [mul_nonneg hp hp']
  have h2 : 0 ≤ a ^ 2 * |p - p'| := by positivity
  nlinarith [abs_nonneg (p - p')]

theorem ric_nonneg (a : ℝ) {q r p : ℝ} (hq : 0 ≤ q) (hr : 0 < r) (hp : 0 ≤ p) :
    0 ≤ ric a q r p := by unfold ric; positivity

open Filter Topology in
/-- For `|a| < 1`, `q > 0`: iterates converge to `dareSS` from any `p₀ ≥ 0`. -/
theorem tendsto_ric_stable {a q r p₀ : ℝ} (ha : a ^ 2 < 1) (hq : 0 < q) (hr : 0 < r)
    (hp₀ : 0 ≤ p₀) :
    Tendsto (fun k => (ric a q r)^[k] p₀) atTop (𝓝 (dareSS a q r)) := by
  have hS := dareSS_pos a hq hr
  have hnn : ∀ k, 0 ≤ (ric a q r)^[k] p₀ := by
    intro k; induction k with
    | zero => exact hp₀
    | succ k ih => rw [Function.iterate_succ_apply']; exact ric_nonneg a hq.le hr ih
  have hb : ∀ k, |(ric a q r)^[k] p₀ - dareSS a q r| ≤ (a ^ 2) ^ k * |p₀ - dareSS a q r| := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc _ = |ric a q r ((ric a q r)^[k] p₀) - ric a q r (dareSS a q r)| := by
              rw [ric_dareSS a hq hr]
        _ ≤ a ^ 2 * |(ric a q r)^[k] p₀ - dareSS a q r| := ric_lipschitz a q hr (hnn k) hS.le
        _ ≤ a ^ 2 * ((a ^ 2) ^ k * |p₀ - dareSS a q r|) := by gcongr
        _ = _ := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun k : ℕ => (a ^ 2) ^ k * |p₀ - dareSS a q r|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg a) ha).mul_const
      |p₀ - dareSS a q r|
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => by rw [Real.norm_eq_abs]; exact hb k) hlim

/-! ### `q = 0`: exact solution in information form -/

/-- With `q = 0` the information `1/p` evolves affinely: `1/p⁺ = (1/p + 1/r) / a²`. -/
theorem inv_ric_q0 {a r p : ℝ} (ha : a ≠ 0) (hr : 0 < r) (hp : 0 < p) :
    (ric a 0 r p)⁻¹ = (p⁻¹ + r⁻¹) / a ^ 2 := by
  unfold ric; field_simp; ring

theorem ric_q0_pos {a r p : ℝ} (ha : a ≠ 0) (hr : 0 < r) (hp : 0 < p) : 0 < ric a 0 r p := by
  unfold ric; have := pow_pos (abs_pos.2 ha) 2; rw [sq_abs] at this; positivity

/-- Closed form: `1/p_k - x* = a^{-2k} (1/p₀ - x*)` with `x* = 1/((a²-1) r)`. -/
theorem inv_iterate_q0 {a r p₀ : ℝ} (ha : 1 < a ^ 2) (hr : 0 < r) (hp₀ : 0 < p₀) (k : ℕ) :
    0 < (ric a 0 r)^[k] p₀ ∧
    ((ric a 0 r)^[k] p₀)⁻¹ - ((a ^ 2 - 1) * r)⁻¹ =
      ((a ^ 2)⁻¹) ^ k * (p₀⁻¹ - ((a ^ 2 - 1) * r)⁻¹) := by
  have ha0 : a ≠ 0 := by rintro rfl; norm_num at ha
  have ha1 : (a ^ 2 - 1) ≠ 0 := by linarith
  induction k with
  | zero => simp [hp₀]
  | succ k ih =>
    obtain ⟨hpos, heq⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨ric_q0_pos ha0 hr hpos, ?_⟩
    have : a ^ 2 ≠ 0 := by positivity
    rw [inv_ric_q0 ha0 hr hpos, pow_succ ((a ^ 2)⁻¹) k, mul_comm (((a ^ 2)⁻¹) ^ k), mul_assoc,
      ← heq]
    field_simp
    ring

open Filter Topology in
/-- **Unstable `a`, no process noise**: `p_k → (a² - 1) r ≠ 0` from any `p₀ > 0`.
(The fixed point `0` is repelling.) -/
theorem tendsto_ric_q0_unstable {a r p₀ : ℝ} (ha : 1 < a ^ 2) (hr : 0 < r) (hp₀ : 0 < p₀) :
    Tendsto (fun k => (ric a 0 r)^[k] p₀) atTop (𝓝 ((a ^ 2 - 1) * r)) := by
  have hx : Tendsto (fun k => ((ric a 0 r)^[k] p₀)⁻¹) atTop (𝓝 ((a ^ 2 - 1) * r)⁻¹) := by
    have h0 : Tendsto (fun k : ℕ => ((a ^ 2)⁻¹) ^ k * (p₀⁻¹ - ((a ^ 2 - 1) * r)⁻¹))
        atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ ha)).mul_const (p₀⁻¹ - ((a ^ 2 - 1) * r)⁻¹)
      rw [zero_mul] at h; exact h
    have := h0.add_const ((a ^ 2 - 1) * r)⁻¹
    simp only [zero_add] at this
    refine this.congr fun k => ?_
    rw [← (inv_iterate_q0 ha hr hp₀ k).2]; ring
  have hL : (a ^ 2 - 1) * r ≠ 0 := by have : 0 < a ^ 2 - 1 := by linarith
                                      positivity
  simpa using hx.inv₀ (inv_ne_zero hL)

/-- And `(a² - 1) r` is exactly `dareSS a 0 r` when `|a| > 1`. -/
theorem dareSS_q0_unstable {a r : ℝ} (ha : 1 < a ^ 2) (hr : 0 < r) :
    dareSS a 0 r = (a ^ 2 - 1) * r := by
  unfold dareSS
  have : 0 ≤ (a ^ 2 - 1) * r := by have : 0 < a ^ 2 - 1 := by linarith
                                   positivity
  simp [Real.sqrt_sq this]

/-- But for `|a| ≤ 1`, `q = 0`, `dareSS a 0 r = 0`. -/
theorem dareSS_q0_stable {a r : ℝ} (ha : a ^ 2 ≤ 1) (hr : 0 < r) : dareSS a 0 r = 0 := by
  unfold dareSS
  simp [Real.sqrt_sq_eq_abs, abs_of_nonpos (show (a ^ 2 - 1) * r ≤ 0 by nlinarith)]

open Filter Topology in
/-- Stable `a`, `q = 0`: variance collapses to `0` geometrically (rate `a²`). -/
theorem tendsto_ric_q0_stable {a r p₀ : ℝ} (ha : a ^ 2 < 1) (hr : 0 < r) (hp₀ : 0 ≤ p₀) :
    Tendsto (fun k => (ric a 0 r)^[k] p₀) atTop (𝓝 0) := by
  have hnn : ∀ k, 0 ≤ (ric a 0 r)^[k] p₀ := by
    intro k; induction k with
    | zero => exact hp₀
    | succ k ih => rw [Function.iterate_succ_apply']; exact ric_nonneg a le_rfl hr ih
  have hb : ∀ k, (ric a 0 r)^[k] p₀ ≤ (a ^ 2) ^ k * p₀ := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h := ric_lipschitz a 0 hr (hnn k) le_rfl
      have h0 : ric a 0 r 0 = 0 := by unfold ric; simp
      rw [h0, sub_zero, sub_zero, abs_of_nonneg (ric_nonneg a le_rfl hr (hnn k)),
        abs_of_nonneg (hnn k)] at h
      calc _ ≤ a ^ 2 * (ric a 0 r)^[k] p₀ := h
        _ ≤ a ^ 2 * ((a ^ 2) ^ k * p₀) := by gcongr
        _ = _ := by ring
  have hlim : Tendsto (fun k : ℕ => (a ^ 2) ^ k * p₀) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg a) ha).mul_const p₀
    rw [zero_mul] at h; exact h
  exact squeeze_zero hnn hb hlim

/-! ### Closed-loop stability and convergence for every `a` (incl. `|a| > 1`) -/

/-- Fixed-point equation cleared of denominators. -/
theorem dareSS_fixed_cleared (a : ℝ) {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    dareSS a q r * (dareSS a q r + r) = a ^ 2 * dareSS a q r * r + q * (dareSS a q r + r) := by
  have hS := dareSS_pos a hq hr
  have h := ric_dareSS a hq hr
  unfold ric at h
  have hne : dareSS a q r + r ≠ 0 := by positivity
  field_simp at h
  linarith

/-- **Closed-loop stability of the steady-state Kalman filter**: the error dynamics
`e⁺ = a (1 - K) e` with `K = p*/(p*+r)` have `|a (1 - K)| = |a| r / (p* + r) < 1`,
for every `a` (stable or not), `q > 0`, `r > 0`. -/
theorem closedLoop_stable (a : ℝ) {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    |a * (1 - dareSS a q r / (dareSS a q r + r))| < 1 := by
  have hS := dareSS_pos a hq hr
  set S := dareSS a q r
  have hfix := dareSS_fixed_cleared a hq hr
  have hSr : 0 < S + r := by positivity
  have e : a * (1 - S / (S + r)) = a * r / (S + r) := by field_simp; ring
  rw [e, abs_div, abs_of_pos hSr, div_lt_one hSr, abs_mul, abs_of_pos hr]
  -- S ((S+r)² - a² r²) = (S+r)(S² + r q) > 0
  have key : S * ((S + r) ^ 2 - a ^ 2 * r ^ 2) = (S + r) * (S ^ 2 + r * q) := by
    linear_combination r * hfix
  have hpos : 0 < (S + r) ^ 2 - a ^ 2 * r ^ 2 := by
    have : 0 < S * ((S + r) ^ 2 - a ^ 2 * r ^ 2) := by rw [key]; positivity
    exact pos_of_mul_pos_right this hS.le
  have h1 : (|a| * r) ^ 2 < (S + r) ^ 2 := by rw [mul_pow, sq_abs]; linarith
  have h0 : 0 ≤ |a| * r := by positivity
  by_contra hc; push Not at hc
  nlinarith

/-- Squared form: `a² r² / (p* + r)² < 1`. -/
theorem closedLoop_sq_lt_one (a : ℝ) {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    a ^ 2 * r ^ 2 / (dareSS a q r + r) ^ 2 < 1 := by
  have h := closedLoop_stable a hq hr
  have hS := dareSS_pos a hq hr
  have hSr : 0 < dareSS a q r + r := by positivity
  have e : a * (1 - dareSS a q r / (dareSS a q r + r)) = a * r / (dareSS a q r + r) := by
    field_simp; ring
  rw [e] at h
  have h2 := (sq_lt_one_iff_abs_lt_one _).2 h
  rw [div_pow, mul_pow] at h2
  exact h2

/-- Below the steady state, the map moves up. -/
theorem le_ric_of_le_dareSS (a : ℝ) {q r p : ℝ} (hq : 0 < q) (hr : 0 < r) (hp : 0 ≤ p)
    (hpS : p ≤ dareSS a q r) : p ≤ ric a q r p := by
  have hne : 0 < p + r := by positivity
  have e := dare_quad_eq (a := a) (q := q) hne.ne'
  rw [quad_factor a q r p hq.le hr.le] at e
  have hn := dareSSneg_nonpos a q r hq.le hr.le
  have : (p + r) * (p - ric a q r p) ≤ 0 := by
    rw [e]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  by_contra hc; push Not at hc
  have : 0 < (p + r) * (p - ric a q r p) := mul_pos hne (by linarith)
  linarith

/-- Above the steady state: one-sided contraction with factor `c = a² r² / (p* + r)² < 1`. -/
theorem ric_sub_dareSS_above (a : ℝ) {q r p : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hpS : dareSS a q r ≤ p) :
    0 ≤ ric a q r p - dareSS a q r ∧
    ric a q r p - dareSS a q r ≤
      a ^ 2 * r ^ 2 / (dareSS a q r + r) ^ 2 * (p - dareSS a q r) := by
  have hS := dareSS_pos a hq hr
  set S := dareSS a q r
  have hp : 0 < p := hS.trans_le hpS
  have e : ric a q r p - S = a ^ 2 * r ^ 2 / ((p + r) * (S + r)) * (p - S) := by
    rw [show ric a q r p - S = ric a q r p - ric a q r S by rw [ric_dareSS a hq hr]]
    unfold ric; field_simp; ring
  rw [e]
  refine ⟨by have := sub_nonneg.2 hpS; positivity, ?_⟩
  gcongr
  rw [sq]; gcongr

open Filter Topology in
/-- **Riccati convergence for every `a`** (including unstable `|a| > 1`), `q > 0`, `r > 0`,
from any `p₀ ≥ 0`. -/
theorem tendsto_ric (a : ℝ) {q r p₀ : ℝ} (hq : 0 < q) (hr : 0 < r) (hp₀ : 0 ≤ p₀) :
    Tendsto (fun k => (ric a q r)^[k] p₀) atTop (𝓝 (dareSS a q r)) := by
  have hS := dareSS_pos a hq hr
  set S := dareSS a q r
  set x : ℕ → ℝ := fun k => (ric a q r)^[k] p₀ with hx
  have hsucc : ∀ k, x (k + 1) = ric a q r (x k) := fun k => Function.iterate_succ_apply' _ _ _
  rcases le_total p₀ S with hlo | hhi
  · -- monotone increasing, bounded by S
    have hb : ∀ k, 0 ≤ x k ∧ x k ≤ S := by
      intro k; induction k with
      | zero => exact ⟨hp₀, hlo⟩
      | succ k ih =>
        rw [hsucc]
        exact ⟨ric_nonneg a hq.le hr ih.1,
          (ric_mono_p a q hr ih.1 ih.2).trans (ric_dareSS a hq hr).le⟩
    have hmono : Monotone x := monotone_nat_of_le_succ fun k => by
      rw [hsucc]; exact le_ric_of_le_dareSS a hq hr (hb k).1 (hb k).2
    have hbdd : BddAbove (Set.range x) := ⟨S, by rintro _ ⟨k, rfl⟩; exact (hb k).2⟩
    have hL := tendsto_atTop_ciSup hmono hbdd
    set L := ⨆ k, x k
    have hL0 : 0 ≤ L := le_trans (hb 0).1 (le_ciSup hbdd 0)
    -- continuity of ric at L
    have hcont : ContinuousAt (ric a q r) L := by
      unfold ric
      have : L + r ≠ 0 := by positivity
      fun_prop (disch := assumption)
    have h1 : Tendsto (fun k => x (k + 1)) atTop (𝓝 (ric a q r L)) := by
      simp_rw [hsucc]; exact hcont.tendsto.comp hL
    have h2 : Tendsto (fun k => x (k + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
    have hfix : ric a q r L = L := tendsto_nhds_unique h1 h2
    rw [ric_fixed_unique a hq hr hL0 hfix] at hL
    exact hL
  · -- above S: geometric contraction
    set c := a ^ 2 * r ^ 2 / (S + r) ^ 2
    have hc1 : c < 1 := closedLoop_sq_lt_one a hq hr
    have hc0 : 0 ≤ c := by positivity
    have hb : ∀ k, S ≤ x k ∧ x k - S ≤ c ^ k * (p₀ - S) := by
      intro k; induction k with
      | zero => exact ⟨hhi, by simp [hx]⟩
      | succ k ih =>
        rw [hsucc]
        obtain ⟨h0, h1⟩ := ric_sub_dareSS_above a hq hr ih.1
        refine ⟨by linarith, h1.trans ?_⟩
        calc c * (x k - S) ≤ c * (c ^ k * (p₀ - S)) := by gcongr; exact ih.2
          _ = _ := by ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun k : ℕ => c ^ k * (p₀ - S)) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const (p₀ - S)
      rw [zero_mul] at h; exact h
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hlim
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(hb k).1])]
    exact (hb k).2

end ExploreKalman
