import ControlsLean.Controls.Hurwitz2
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

namespace ControlsLean.Controls

/-- `s³ + a s² + b s + c` has all complex roots in the open left half-plane. -/
def IsHurwitz3 (a b c : ℝ) : Prop :=
  ∀ z : ℂ, z ^ 3 + a * z ^ 2 + b * z + c = 0 → z.re < 0

lemma cubic_root_parts {a b c : ℝ} {z : ℂ} (h : z ^ 3 + a * z ^ 2 + b * z + c = 0) :
    z.re ^ 3 - 3 * z.re * z.im ^ 2 + a * (z.re ^ 2 - z.im ^ 2) + b * z.re + c = 0 ∧
    z.im * (3 * z.re ^ 2 - z.im ^ 2 + 2 * a * z.re + b) = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_succ] at hre him
  constructor <;> nlinarith

/-- Sufficiency of the third-order Routh–Hurwitz conditions. -/
theorem isHurwitz3_of_routh {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : c < a * b) : IsHurwitz3 a b c := by
  intro z hz
  obtain ⟨hre, him⟩ := cubic_root_parts hz
  by_contra hx
  push Not at hx
  set x := z.re
  set y := z.im
  rcases mul_eq_zero.1 him with hy | hq
  · rw [hy] at hre
    nlinarith [pow_nonneg hx 3, sq_nonneg x, mul_nonneg ha.le (sq_nonneg x),
      mul_nonneg hb.le hx]
  · have hy2 : y ^ 2 = 3 * x ^ 2 + 2 * a * x + b := by linarith
    have key : -8 * x ^ 3 - 8 * a * x ^ 2 - (2 * b + 2 * a ^ 2) * x + (c - a * b) = 0 := by
      have : y ^ 2 = 3 * x ^ 2 + 2 * a * x + b := hy2
      nlinarith
    nlinarith [pow_nonneg hx 3, mul_nonneg ha.le (sq_nonneg x),
      mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * b + 2 * a ^ 2) hx]

/-- Every real cubic has a real root (IVT). -/
lemma exists_real_root_cubic (a b c : ℝ) : ∃ r : ℝ, r ^ 3 + a * r ^ 2 + b * r + c = 0 := by
  set M := 1 + |a| + |b| + |c|
  have hM : 1 ≤ M := by
    have := abs_nonneg a; have := abs_nonneg b; have := abs_nonneg c; simp only [M]; linarith
  have f_cont : Continuous fun r : ℝ => r ^ 3 + a * r ^ 2 + b * r + c := by fun_prop
  have hlo : (-M) ^ 3 + a * (-M) ^ 2 + b * (-M) + c ≤ 0 := by
    have h1 : a ≤ |a| := le_abs_self a
    have h2 : -b ≤ |b| := neg_le_abs b
    have h3 : c ≤ |c| := le_abs_self c
    have hM2 : M ≤ M ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg M),
      mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ M),
      abs_nonneg a, abs_nonneg b, abs_nonneg c, mul_le_mul_of_nonneg_left hM2 (abs_nonneg b),
      mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ M ^ 2) (abs_nonneg c)]
  have hhi : 0 ≤ M ^ 3 + a * M ^ 2 + b * M + c := by
    have h1 : -a ≤ |a| := neg_le_abs a
    have h2 : -b ≤ |b| := neg_le_abs b
    have h3 : -c ≤ |c| := neg_le_abs c
    have hM2 : M ≤ M ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg M),
      mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ M),
      abs_nonneg a, abs_nonneg b, abs_nonneg c, mul_le_mul_of_nonneg_left hM2 (abs_nonneg b),
      mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ M ^ 2) (abs_nonneg c)]
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc (by linarith : -M ≤ M) f_cont.continuousOn
    ⟨hlo, hhi⟩
  exact ⟨r, hr⟩

/-- Necessity of the third-order Routh–Hurwitz conditions, via real-root factorization
`s³ + a s² + b s + c = (s - r)(s² + p s + q)`. -/
theorem routh_of_isHurwitz3 {a b c : ℝ} (h : IsHurwitz3 a b c) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ c < a * b := by
  obtain ⟨r, hr⟩ := exists_real_root_cubic a b c
  have hr0 : r < 0 := by
    have := h r (by exact_mod_cast hr)
    simpa using this
  set p := a + r
  set q := b + r * p
  have hc : c = -r * q := by simp only [p, q]; nlinarith
  have h2 : IsHurwitz2 p q := by
    intro z hz
    apply h z
    have hp' : (p : ℂ) = a + r := by simp [p]
    have hq' : (q : ℂ) = b + r * p := by simp [q]
    have hc' : (c : ℂ) = -r * q := by exact_mod_cast hc
    have hfac : z ^ 3 + a * z ^ 2 + b * z + c = (z - r) * (z ^ 2 + p * z + q) := by
      linear_combination (-z ^ 2) * hp' + (-z) * hq' + hc'
    rw [hfac, hz, mul_zero]
  obtain ⟨hp, hq⟩ := (isHurwitz2_iff p q).1 h2
  have ha : a = p - r := by simp [p]
  have hb : b = q - r * p := by simp [q]
  refine ⟨by linarith, by nlinarith, by rw [hc]; nlinarith, ?_⟩
  rw [ha, hb, hc]
  nlinarith [mul_pos (mul_pos hp hp) (neg_pos.2 hr0), mul_pos hp (mul_pos (neg_pos.2 hr0) (neg_pos.2 hr0))]

/-- **Third-order Routh–Hurwitz criterion.** -/
theorem isHurwitz3_iff (a b c : ℝ) :
    IsHurwitz3 a b c ↔ 0 < a ∧ 0 < b ∧ 0 < c ∧ c < a * b :=
  ⟨routh_of_isHurwitz3, fun ⟨ha, hb, hc, h⟩ => isHurwitz3_of_routh ha hb hc h⟩

/-- PID on a double integrator: `ÿ = u`, `u = -kp y - kd ẏ - ki ∫y` gives
`s³ + kd s² + kp s + ki`; stable iff `kd, kp, ki > 0` and `ki < kd kp`. -/
theorem pid_doubleIntegrator_hurwitz_iff (kp ki kd : ℝ) :
    IsHurwitz3 kd kp ki ↔ 0 < kd ∧ 0 < kp ∧ 0 < ki ∧ ki < kd * kp :=
  isHurwitz3_iff kd kp ki

/-- Boundary case: `ab = c` gives a pure imaginary pair `±i√b`, so not Hurwitz. -/
example : ¬ IsHurwitz3 1 1 1 := by
  intro h
  have := h Complex.I (by ring_nf; simp [Complex.I_sq])
  simp at this

/-! ## Kharitonov (1978) for degrees 2 and 3 -/

/-- `c₃ s³ + c₂ s² + c₁ s + c₀` has all complex roots in the open left half-plane. -/
def HurwitzCubic (c₀ c₁ c₂ c₃ : ℝ) : Prop :=
  ∀ z : ℂ, c₃ * z ^ 3 + c₂ * z ^ 2 + c₁ * z + c₀ = 0 → z.re < 0

/-- `c₂ s² + c₁ s + c₀` has all complex roots in the open left half-plane. -/
def HurwitzQuad (c₀ c₁ c₂ : ℝ) : Prop :=
  ∀ z : ℂ, c₂ * z ^ 2 + c₁ * z + c₀ = 0 → z.re < 0

lemma hurwitzCubic_iff_monic {c₀ c₁ c₂ c₃ : ℝ} (h3 : 0 < c₃) :
    HurwitzCubic c₀ c₁ c₂ c₃ ↔ IsHurwitz3 (c₂ / c₃) (c₁ / c₃) (c₀ / c₃) := by
  have hne : (c₃ : ℂ) ≠ 0 := by exact_mod_cast h3.ne'
  refine forall_congr' fun z => ?_
  have : (c₃ : ℂ) * z ^ 3 + c₂ * z ^ 2 + c₁ * z + c₀ =
      c₃ * (z ^ 3 + ((c₂ / c₃ : ℝ) : ℂ) * z ^ 2 + ((c₁ / c₃ : ℝ) : ℂ) * z + ((c₀ / c₃ : ℝ) : ℂ)) := by
    push_cast; field_simp
  rw [this, mul_eq_zero, or_iff_right hne]

lemma hurwitzQuad_iff_monic {c₀ c₁ c₂ : ℝ} (h2 : 0 < c₂) :
    HurwitzQuad c₀ c₁ c₂ ↔ IsHurwitz2 (c₁ / c₂) (c₀ / c₂) := by
  have hne : (c₂ : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  refine forall_congr' fun z => ?_
  have : (c₂ : ℂ) * z ^ 2 + c₁ * z + c₀ =
      c₂ * (z ^ 2 + ((c₁ / c₂ : ℝ) : ℂ) * z + ((c₀ / c₂ : ℝ) : ℂ)) := by
    push_cast; field_simp
  rw [this, mul_eq_zero, or_iff_right hne]

/-- Routh–Hurwitz for a non-monic cubic with positive leading coefficient. -/
theorem hurwitzCubic_iff {c₀ c₁ c₂ c₃ : ℝ} (h3 : 0 < c₃) :
    HurwitzCubic c₀ c₁ c₂ c₃ ↔ 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ c₃ * c₀ < c₂ * c₁ := by
  rw [hurwitzCubic_iff_monic h3, isHurwitz3_iff, div_pos_iff_of_pos_right h3,
    div_pos_iff_of_pos_right h3, div_pos_iff_of_pos_right h3]
  have : c₀ / c₃ < c₂ / c₃ * (c₁ / c₃) ↔ c₃ * c₀ < c₂ * c₁ := by
    rw [div_mul_div_comm, div_lt_div_iff₀ h3 (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [this]; tauto

theorem hurwitzQuad_iff {c₀ c₁ c₂ : ℝ} (h2 : 0 < c₂) :
    HurwitzQuad c₀ c₁ c₂ ↔ 0 < c₀ ∧ 0 < c₁ := by
  rw [hurwitzQuad_iff_monic h2, isHurwitz2_iff, div_pos_iff_of_pos_right h2,
    div_pos_iff_of_pos_right h2, and_comm]

/-- Interval family `{∑ cᵢ sⁱ : cᵢ ∈ [lᵢ, uᵢ]}` of cubics. -/
def IntervalCubicHurwitz (l u : Fin 4 → ℝ) : Prop :=
  ∀ c : Fin 4 → ℝ, (∀ i, c i ∈ Set.Icc (l i) (u i)) → HurwitzCubic (c 0) (c 1) (c 2) (c 3)

def IntervalQuadHurwitz (l u : Fin 3 → ℝ) : Prop :=
  ∀ c : Fin 3 → ℝ, (∀ i, c i ∈ Set.Icc (l i) (u i)) → HurwitzQuad (c 0) (c 1) (c 2)

/-- **Kharitonov, degree 2**: a quadratic interval family (with positive leading lower bound)
is robustly Hurwitz iff all coefficient lower bounds are positive. -/
theorem kharitonov2 (l u : Fin 3 → ℝ) (hlu : ∀ i, l i ≤ u i) (h2 : 0 < l 2) :
    IntervalQuadHurwitz l u ↔ 0 < l 0 ∧ 0 < l 1 := by
  constructor
  · intro h
    have := h l (fun i => ⟨le_rfl, hlu i⟩)
    exact (hurwitzQuad_iff h2).1 this
  · rintro ⟨h0, h1⟩ c hc
    have := hc 0; have := hc 1; have := hc 2
    rw [hurwitzQuad_iff (by simp only [Set.mem_Icc] at *; linarith)]
    simp only [Set.mem_Icc] at *
    constructor <;> linarith

/-- **Kharitonov, degree 3, sharp form** (cf. Anderson–Jury–Mansour 1987): only the single
vertex `u₀ + l₁ s + l₂ s² + u₃ s³` plus `l₀ > 0` needs to be checked. -/
theorem kharitonov3_single (l u : Fin 4 → ℝ) (hlu : ∀ i, l i ≤ u i) (h3 : 0 < l 3) :
    IntervalCubicHurwitz l u ↔ 0 < l 0 ∧ HurwitzCubic (u 0) (l 1) (l 2) (u 3) := by
  have hu3 : 0 < u 3 := lt_of_lt_of_le h3 (hlu 3)
  constructor
  · intro h
    refine ⟨((hurwitzCubic_iff h3).1 (h l fun i => ⟨le_rfl, hlu i⟩)).1, ?_⟩
    apply h ![u 0, l 1, l 2, u 3]
    intro i; fin_cases i <;> simp [hlu]
  · rintro ⟨h0, hK⟩ c hc
    obtain ⟨-, h1, h2, hR⟩ := (hurwitzCubic_iff hu3).1 hK
    have := hc 0; have := hc 1; have := hc 2; have := hc 3
    simp only [Set.mem_Icc] at *
    rw [hurwitzCubic_iff (by linarith)]
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    nlinarith [mul_le_mul (show c 3 ≤ u 3 by linarith) (show c 0 ≤ u 0 by linarith)
      (by linarith) hu3.le,
      mul_le_mul (show l 2 ≤ c 2 by linarith) (show l 1 ≤ c 1 by linarith) h1.le (by linarith)]

/-- **Kharitonov's theorem, degree 3** (four-vertex form, Kharitonov 1978).
Coefficients are listed in ascending powers: `K(c₀,c₁,c₂,c₃) = c₀ + c₁ s + c₂ s² + c₃ s³`. -/
theorem kharitonov3 (l u : Fin 4 → ℝ) (hlu : ∀ i, l i ≤ u i) (h3 : 0 < l 3) :
    IntervalCubicHurwitz l u ↔
      HurwitzCubic (l 0) (l 1) (u 2) (u 3) ∧ HurwitzCubic (u 0) (u 1) (l 2) (l 3) ∧
      HurwitzCubic (l 0) (u 1) (u 2) (l 3) ∧ HurwitzCubic (u 0) (l 1) (l 2) (u 3) := by
  constructor
  · intro h
    refine ⟨h ![l 0, l 1, u 2, u 3] ?_, h ![u 0, u 1, l 2, l 3] ?_,
      h ![l 0, u 1, u 2, l 3] ?_, h ![u 0, l 1, l 2, u 3] ?_⟩ <;>
    · intro i; fin_cases i <;> simp [hlu]
  · rintro ⟨hK1, -, -, hK4⟩
    have hu3 : 0 < u 3 := lt_of_lt_of_le h3 (hlu 3)
    exact (kharitonov3_single l u hlu h3).2 ⟨((hurwitzCubic_iff hu3).1 hK1).1, hK4⟩

/-! ### Application: mass–spring–damper with uncertain `m, c, k` -/

/-- PD control `u = -kp y - kd ẏ` of `m ÿ + c ẏ + k y = u` is stable for **every**
`m ∈ [m₁,m₂], c ∈ [c₁,c₂], k ∈ [k₁,k₂]` iff `c₁ + kd > 0` and `k₁ + kp > 0`. -/
theorem msd_pd_robust {m₁ m₂ c₁ c₂ k₁ k₂ kp kd : ℝ} (hm : 0 < m₁) (hm' : m₁ ≤ m₂)
    (hc : c₁ ≤ c₂) (hk : k₁ ≤ k₂) :
    (∀ m ∈ Set.Icc m₁ m₂, ∀ c ∈ Set.Icc c₁ c₂, ∀ k ∈ Set.Icc k₁ k₂,
      HurwitzQuad (k + kp) (c + kd) m) ↔ 0 < c₁ + kd ∧ 0 < k₁ + kp := by
  constructor
  · intro h
    have := (hurwitzQuad_iff hm).1 (h m₁ ⟨le_rfl, hm'⟩ c₁ ⟨le_rfl, hc⟩ k₁ ⟨le_rfl, hk⟩)
    exact ⟨this.2, this.1⟩
  · rintro ⟨h1, h2⟩ m ⟨hm1, -⟩ c ⟨hc1, -⟩ k ⟨hk1, -⟩
    rw [hurwitzQuad_iff (by linarith)]
    constructor <;> linarith

/-- PID control `u = -kp y - kd ẏ - ki ∫ y` of `m ÿ + c ẏ + k y = u` gives
`m s³ + (c+kd) s² + (k+kp) s + ki`. It is stable for **every** parameter in the box iff the
single Kharitonov vertex (heaviest mass, least damping, softest spring) satisfies Routh. -/
theorem msd_pid_robust {m₁ m₂ c₁ c₂ k₁ k₂ kp ki kd : ℝ} (hm : 0 < m₁) (hm' : m₁ ≤ m₂)
    (hc : c₁ ≤ c₂) (hk : k₁ ≤ k₂) :
    (∀ m ∈ Set.Icc m₁ m₂, ∀ c ∈ Set.Icc c₁ c₂, ∀ k ∈ Set.Icc k₁ k₂,
      HurwitzCubic ki (k + kp) (c + kd) m) ↔
      0 < ki ∧ 0 < k₁ + kp ∧ 0 < c₁ + kd ∧ m₂ * ki < (c₁ + kd) * (k₁ + kp) := by
  constructor
  · intro h
    exact (hurwitzCubic_iff (by linarith)).1
      (h m₂ ⟨hm', le_rfl⟩ c₁ ⟨le_rfl, hc⟩ k₁ ⟨le_rfl, hk⟩)
  · rintro ⟨h0, h1, h2, hR⟩ m ⟨hm1, hm2⟩ c ⟨hc1, -⟩ k ⟨hk1, -⟩
    rw [hurwitzCubic_iff (by linarith)]
    refine ⟨h0, by linarith, by linarith, ?_⟩
    nlinarith [mul_le_mul (show c₁ + kd ≤ c + kd by linarith) (show k₁ + kp ≤ k + kp by linarith)
      h1.le (by linarith), mul_le_mul_of_nonneg_right hm2 h0.le]

/-- Concrete design: `m ∈ [1,2]` kg, `c ∈ [0.1,0.5]`, `k ∈ [1,3]`, `kp = 4, kd = 2`.
The integral gain is robustly safe exactly for `0 < ki < 5.25`; `ki = 5` works. -/
example : ∀ m ∈ Set.Icc (1 : ℝ) 2, ∀ c ∈ Set.Icc (0.1 : ℝ) 0.5, ∀ k ∈ Set.Icc (1 : ℝ) 3,
    HurwitzCubic 5 (k + 4) (c + 2) m :=
  (msd_pid_robust (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- ... and `ki = 5.5` is destabilized by some admissible plant. -/
example : ¬ ∀ m ∈ Set.Icc (1 : ℝ) 2, ∀ c ∈ Set.Icc (0.1 : ℝ) 0.5, ∀ k ∈ Set.Icc (1 : ℝ) 3,
    HurwitzCubic 5.5 (k + 4) (c + 2) m := by
  rw [msd_pid_robust (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end ControlsLean.Controls
