import Mathlib.Analysis.Complex.Polynomial.Basic
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


/-! ## Quartic Routh–Hurwitz -/

/-- `s⁴ + a s³ + b s² + c s + d` has all complex roots in the open left half-plane. -/
def IsHurwitz4 (a b c d : ℝ) : Prop :=
  ∀ z : ℂ, z ^ 4 + a * z ^ 3 + b * z ^ 2 + c * z + d = 0 → z.re < 0

/-- Third Hurwitz determinant of `(s² + α s + β)(s² + γ s + δ)`. -/
lemma quartic_delta_identity (α β γ δ : ℝ) :
    (α + γ) * (β + δ + α * γ) * (α * δ + β * γ) - (α * δ + β * γ) ^ 2 - (α + γ) ^ 2 * (β * δ)
      = α * γ * ((β - δ) ^ 2 + (α + γ) * (α * δ + β * γ)) := by ring

lemma exists_root_quartic (a b c d : ℝ) :
    ∃ z : ℂ, z ^ 4 + a * z ^ 3 + b * z ^ 2 + c * z + d = 0 := by
  open Polynomial in
  have hnat : (X ^ 4 + C (a : ℂ) * X ^ 3 + C (b : ℂ) * X ^ 2 + C (c : ℂ) * X + C (d : ℂ) :
      ℂ[X]).natDegree = 4 := by compute_degree!
  have hdeg : 0 < (X ^ 4 + C (a : ℂ) * X ^ 3 + C (b : ℂ) * X ^ 2 + C (c : ℂ) * X + C (d : ℂ) :
      ℂ[X]).degree := by
    rw [degree_eq_natDegree (fun h => by rw [h] at hnat; simp at hnat), hnat]; norm_num
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  exact ⟨z, by simpa [IsRoot] using hz⟩

/-- A non-real root `z = x + iy` splits off the real factor `s² - 2x s + (x² + y²)`. -/
lemma factor_of_nonreal_root {a b c d x y : ℝ}
    (hz : (⟨x, y⟩ : ℂ) ^ 4 + a * (⟨x, y⟩ : ℂ) ^ 3 + b * (⟨x, y⟩ : ℂ) ^ 2 + c * ⟨x, y⟩ + d = 0)
    (hy : y ≠ 0) :
    ∃ γ δ : ℝ, a = -2 * x + γ ∧ b = (x ^ 2 + y ^ 2) + δ + (-2 * x) * γ ∧
      c = (-2 * x) * δ + (x ^ 2 + y ^ 2) * γ ∧ d = (x ^ 2 + y ^ 2) * δ := by
  set z : ℂ := ⟨x, y⟩ with hzdef
  have hq : z ^ 2 - 2 * (x : ℂ) * z + ((x ^ 2 + y ^ 2 : ℝ) : ℂ) = 0 := by
    apply Complex.ext <;> simp [z, pow_two] <;> ring
  set r : ℝ := x ^ 2 + y ^ 2
  set P : ℝ := a + 2 * x with hP
  set Q : ℝ := b + 2 * x * P - r with hQ
  have hlin : ((c - (-2 * x * Q + r * P) : ℝ) : ℂ) * z + ((d - r * Q : ℝ) : ℂ) = 0 := by
    have e : ((c - (-2 * x * Q + r * P) : ℝ) : ℂ) * z + ((d - r * Q : ℝ) : ℂ) =
        (z ^ 4 + a * z ^ 3 + b * z ^ 2 + c * z + d) -
          (z ^ 2 - 2 * (x : ℂ) * z + (r : ℂ)) * (z ^ 2 + P * z + Q) := by
      simp only [hQ, hP]; push_cast; ring
    rw [e, hz, hq]; ring
  have him := congrArg Complex.im hlin
  have hre := congrArg Complex.re hlin
  simp [z] at him hre
  have h1' := him.resolve_right hy
  have h1 : c - (-2 * x * Q + r * P) = 0 := by linarith
  rw [h1', zero_mul, zero_add] at hre
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · simp only [hP]; ring
  · simp only [hQ, hP]; ring
  · linarith
  · linarith

/-- Every real monic quartic factors into two real monic quadratics. -/
lemma quartic_real_factor (a b c d : ℝ) :
    ∃ α β γ δ : ℝ, a = α + γ ∧ b = β + δ + α * γ ∧ c = α * δ + β * γ ∧ d = β * δ := by
  obtain ⟨z, hz⟩ := exists_root_quartic a b c d
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, z = ⟨x, y⟩ := ⟨z.re, z.im, rfl⟩
  by_cases hy : y = 0
  · subst hy
    have hx : x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
      have : (⟨x, 0⟩ : ℂ) = (x : ℂ) := rfl
      rw [this] at hz; exact_mod_cast hz
    obtain ⟨w, hw⟩ := exists_real_root_cubic (a + x) (b + x * (a + x)) (c + x * (b + x * (a + x)))
    refine ⟨-(x + w), x * w, a + x + w, b + x * (a + x) + w * (a + x + w), by ring, by ring,
      by linear_combination hw, by linear_combination hx - x * hw⟩
  · obtain ⟨γ, δ, h⟩ := factor_of_nonreal_root hz hy
    exact ⟨_, _, γ, δ, h⟩

/-- Sufficiency of the fourth-order Routh–Hurwitz conditions. -/
theorem isHurwitz4_of_routh {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hΔ : c ^ 2 + a ^ 2 * d < a * b * c) : IsHurwitz4 a b c d := by
  intro z hz
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, z = ⟨x, y⟩ := ⟨z.re, z.im, rfl⟩
  show x < 0
  by_contra hx
  push Not at hx
  by_cases hy : y = 0
  · subst hy
    have hx' : x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
      have : (⟨x, 0⟩ : ℂ) = (x : ℂ) := rfl
      rw [this] at hz; exact_mod_cast hz
    nlinarith [pow_nonneg hx 4, mul_nonneg ha.le (pow_nonneg hx 3),
      mul_nonneg hb.le (pow_nonneg hx 2), mul_nonneg hc.le hx]
  · obtain ⟨γ, δ, rfl, rfl, rfl, rfl⟩ := factor_of_nonreal_root hz hy
    have hid := quartic_delta_identity (-2 * x) (x ^ 2 + y ^ 2) γ δ
    have hγ : 0 < γ := by linarith
    have hbr : 0 < ((x ^ 2 + y ^ 2) - δ) ^ 2 + (-2 * x + γ) * ((-2 * x) * δ + (x ^ 2 + y ^ 2) * γ) :=
      by nlinarith [sq_nonneg ((x ^ 2 + y ^ 2) - δ), mul_pos ha hc]
    have hαγ : (-2 * x) * γ ≤ 0 := by nlinarith
    nlinarith [mul_nonpos_iff.2 (Or.inr ⟨hαγ, hbr.le⟩)]

/-- Necessity of the fourth-order Routh–Hurwitz conditions. -/
theorem routh_of_isHurwitz4 {a b c d : ℝ} (h : IsHurwitz4 a b c d) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ c ^ 2 + a ^ 2 * d < a * b * c := by
  obtain ⟨α, β, γ, δ, rfl, rfl, rfl, rfl⟩ := quartic_real_factor a b c d
  have hfac : ∀ u : ℂ, u ^ 4 + ((α + γ : ℝ) : ℂ) * u ^ 3 + ((β + δ + α * γ : ℝ) : ℂ) * u ^ 2 +
      ((α * δ + β * γ : ℝ) : ℂ) * u + ((β * δ : ℝ) : ℂ) =
      (u ^ 2 + α * u + β) * (u ^ 2 + γ * u + δ) := fun u => by push_cast; ring
  have h1 : IsHurwitz2 α β := fun u hu => h u (by rw [hfac, hu, zero_mul])
  have h2 : IsHurwitz2 γ δ := fun u hu => h u (by rw [hfac, hu, mul_zero])
  obtain ⟨hα, hβ⟩ := (isHurwitz2_iff α β).1 h1
  obtain ⟨hγ, hδ⟩ := (isHurwitz2_iff γ δ).1 h2
  refine ⟨by positivity, by positivity, by positivity, by positivity, ?_⟩
  have hid := quartic_delta_identity α β γ δ
  have : 0 < α * γ * ((β - δ) ^ 2 + (α + γ) * (α * δ + β * γ)) := by positivity
  linarith

/-- **Fourth-order Routh–Hurwitz criterion** (Routh 1877, Hurwitz 1895). -/
theorem isHurwitz4_iff (a b c d : ℝ) :
    IsHurwitz4 a b c d ↔ 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ c ^ 2 + a ^ 2 * d < a * b * c :=
  ⟨routh_of_isHurwitz4, fun ⟨ha, hb, hc, hd, h⟩ => isHurwitz4_of_routh ha hb hc hd h⟩

/-! ## Kharitonov, degree 4 -/

/-- `c₄ s⁴ + c₃ s³ + c₂ s² + c₁ s + c₀` has all roots in the open left half-plane. -/
def HurwitzQuartic (c₀ c₁ c₂ c₃ c₄ : ℝ) : Prop :=
  ∀ z : ℂ, c₄ * z ^ 4 + c₃ * z ^ 3 + c₂ * z ^ 2 + c₁ * z + c₀ = 0 → z.re < 0

/-- Routh–Hurwitz for a non-monic quartic with positive leading coefficient. -/
theorem hurwitzQuartic_iff {c₀ c₁ c₂ c₃ c₄ : ℝ} (h4 : 0 < c₄) :
    HurwitzQuartic c₀ c₁ c₂ c₃ c₄ ↔
      0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ c₄ * c₁ ^ 2 + c₀ * c₃ ^ 2 < c₃ * c₂ * c₁ := by
  have hne : (c₄ : ℂ) ≠ 0 := by exact_mod_cast h4.ne'
  have hmon : HurwitzQuartic c₀ c₁ c₂ c₃ c₄ ↔
      IsHurwitz4 (c₃ / c₄) (c₂ / c₄) (c₁ / c₄) (c₀ / c₄) := by
    refine forall_congr' fun z => ?_
    have : (c₄ : ℂ) * z ^ 4 + c₃ * z ^ 3 + c₂ * z ^ 2 + c₁ * z + c₀ =
        c₄ * (z ^ 4 + ((c₃ / c₄ : ℝ) : ℂ) * z ^ 3 + ((c₂ / c₄ : ℝ) : ℂ) * z ^ 2 +
          ((c₁ / c₄ : ℝ) : ℂ) * z + ((c₀ / c₄ : ℝ) : ℂ)) := by
      push_cast; field_simp
    rw [this, mul_eq_zero, or_iff_right hne]
  rw [hmon, isHurwitz4_iff]
  simp only [div_pos_iff_of_pos_right h4]
  have key : c₃ / c₄ * (c₂ / c₄) * (c₁ / c₄) - ((c₁ / c₄) ^ 2 + (c₃ / c₄) ^ 2 * (c₀ / c₄)) =
      (c₃ * c₂ * c₁ - (c₄ * c₁ ^ 2 + c₀ * c₃ ^ 2)) / c₄ ^ 3 := by
    field_simp
  have : (c₁ / c₄) ^ 2 + (c₃ / c₄) ^ 2 * (c₀ / c₄) < c₃ / c₄ * (c₂ / c₄) * (c₁ / c₄) ↔
      c₄ * c₁ ^ 2 + c₀ * c₃ ^ 2 < c₃ * c₂ * c₁ := by
    rw [← sub_pos, key, div_pos_iff_of_pos_right (by positivity), sub_pos]
  rw [this]; tauto

/-- Concavity step: `L t - U t² - V` is positive at two slopes `p₁/p₃ ≥ q₁/q₃`,
hence at every slope in between (homogeneous form). -/
lemma concave_between {L U V p₁ p₃ q₁ q₃ x₁ x₃ : ℝ} (hU : 0 ≤ U) (hp₃ : 0 < p₃) (hq₃ : 0 < q₃)
    (hx₃ : 0 < x₃) (hqx : q₁ * x₃ ≤ x₁ * q₃) (hxp : x₁ * p₃ ≤ p₁ * x₃)
    (hp : U * p₁ ^ 2 + V * p₃ ^ 2 < L * p₁ * p₃) (hq : U * q₁ ^ 2 + V * q₃ ^ 2 < L * q₁ * q₃) :
    U * x₁ ^ 2 + V * x₃ ^ 2 < L * x₁ * x₃ := by
  set h : ℝ → ℝ := fun s => L * s - U * s ^ 2 - V
  set tp := p₁ / p₃; set tq := q₁ / q₃; set t := x₁ / x₃
  have hhp : 0 < h tp := by
    have : p₃ ^ 2 * h tp = L * p₁ * p₃ - U * p₁ ^ 2 - V * p₃ ^ 2 := by
      simp only [h, tp]; field_simp
    have := this ▸ (by linarith : 0 < L * p₁ * p₃ - U * p₁ ^ 2 - V * p₃ ^ 2)
    exact pos_of_mul_pos_right this (by positivity)
  have hhq : 0 < h tq := by
    have : q₃ ^ 2 * h tq = L * q₁ * q₃ - U * q₁ ^ 2 - V * q₃ ^ 2 := by
      simp only [h, tq]; field_simp
    have := this ▸ (by linarith : 0 < L * q₁ * q₃ - U * q₁ ^ 2 - V * q₃ ^ 2)
    exact pos_of_mul_pos_right this (by positivity)
  have h1 : tq ≤ t := by rw [div_le_div_iff₀ hq₃ hx₃]; linarith
  have h2 : t ≤ tp := by rw [div_le_div_iff₀ hx₃ hp₃]; linarith
  have hid : (tp - tq) * h t = (t - tq) * h tp + (tp - t) * h tq + U * (tp - tq) * (t - tq) * (tp - t) := by
    simp only [h]; ring
  have ht : 0 < h t := by
    rcases eq_or_lt_of_le (h1.trans h2) with he | hlt
    · have : t = tq := le_antisymm (he ▸ h2) h1
      rw [this]; exact hhq
    · have hR : 0 < (t - tq) * h tp + (tp - t) * h tq + U * (tp - tq) * (t - tq) * (tp - t) := by
        have := mul_nonneg (mul_nonneg (mul_nonneg hU (sub_nonneg.2 hlt.le)) (sub_nonneg.2 h1))
          (sub_nonneg.2 h2)
        rcases eq_or_lt_of_le h1 with e | l
        · rw [← e]; nlinarith
        · nlinarith [mul_pos (sub_pos.2 l) hhp, mul_nonneg (sub_nonneg.2 h2) hhq.le]
      rw [← hid] at hR
      exact pos_of_mul_pos_right hR (sub_nonneg.2 hlt.le)
  have : x₃ ^ 2 * h t = L * x₁ * x₃ - U * x₁ ^ 2 - V * x₃ ^ 2 := by
    simp only [h, t]; field_simp
  nlinarith [mul_pos (pow_pos hx₃ 2) ht]

def IntervalQuarticHurwitz (l u : Fin 5 → ℝ) : Prop :=
  ∀ c : Fin 5 → ℝ, (∀ i, c i ∈ Set.Icc (l i) (u i)) →
    HurwitzQuartic (c 0) (c 1) (c 2) (c 3) (c 4)

/-- **Kharitonov, degree 4, two-vertex form** (Anderson–Jury–Mansour 1987): besides `l₀ > 0`
only `K₂ = (u,u,l,l,u)` and `K₄ = (u,l,l,u,u)` (ascending coefficients) need checking. -/
theorem kharitonov4_two (l u : Fin 5 → ℝ) (hlu : ∀ i, l i ≤ u i) (h4 : 0 < l 4) :
    IntervalQuarticHurwitz l u ↔
      0 < l 0 ∧ HurwitzQuartic (u 0) (u 1) (l 2) (l 3) (u 4) ∧
        HurwitzQuartic (u 0) (l 1) (l 2) (u 3) (u 4) := by
  have hu4 : 0 < u 4 := lt_of_lt_of_le h4 (hlu 4)
  constructor
  · intro h
    refine ⟨((hurwitzQuartic_iff h4).1 (h l fun i => ⟨le_rfl, hlu i⟩)).1,
      h ![u 0, u 1, l 2, l 3, u 4] ?_, h ![u 0, l 1, l 2, u 3, u 4] ?_⟩ <;>
    · intro i; fin_cases i <;> simp [hlu]
  · rintro ⟨h0, hK2, hK4⟩ c hc
    obtain ⟨-, -, -, hl3, hR2⟩ := (hurwitzQuartic_iff hu4).1 hK2
    obtain ⟨hu0, hl1, hl2, -, hR4⟩ := (hurwitzQuartic_iff hu4).1 hK4
    have := hc 0; have := hc 1; have := hc 2; have := hc 3; have := hc 4
    simp only [Set.mem_Icc] at *
    have c1 : 0 < c 1 := by linarith
    have c3 : 0 < c 3 := by linarith
    rw [hurwitzQuartic_iff (by linarith)]
    refine ⟨by linarith, c1, by linarith, c3, ?_⟩
    have hmid : u 4 * c 1 ^ 2 + u 0 * c 3 ^ 2 < l 2 * c 1 * c 3 :=
      concave_between (p₁ := u 1) (p₃ := l 3) (q₁ := l 1) (q₃ := u 3) hu4.le hl3
        (by linarith) c3 (by nlinarith) (by nlinarith) (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right (show c 4 ≤ u 4 by linarith) (sq_nonneg (c 1)),
      mul_le_mul_of_nonneg_right (show c 0 ≤ u 0 by linarith) (sq_nonneg (c 3)),
      mul_le_mul_of_nonneg_right (show l 2 ≤ c 2 by linarith) (mul_pos c1 c3).le]

/-- **Kharitonov's theorem, degree 4**, four-vertex form. -/
theorem kharitonov4 (l u : Fin 5 → ℝ) (hlu : ∀ i, l i ≤ u i) (h4 : 0 < l 4) :
    IntervalQuarticHurwitz l u ↔
      HurwitzQuartic (l 0) (l 1) (u 2) (u 3) (l 4) ∧ HurwitzQuartic (u 0) (u 1) (l 2) (l 3) (u 4) ∧
      HurwitzQuartic (l 0) (u 1) (u 2) (l 3) (l 4) ∧ HurwitzQuartic (u 0) (l 1) (l 2) (u 3) (u 4) := by
  constructor
  · intro h
    refine ⟨h ![l 0, l 1, u 2, u 3, l 4] ?_, h ![u 0, u 1, l 2, l 3, u 4] ?_,
      h ![l 0, u 1, u 2, l 3, l 4] ?_, h ![u 0, l 1, l 2, u 3, u 4] ?_⟩ <;>
    · intro i; fin_cases i <;> simp [hlu]
  · rintro ⟨hK1, hK2, -, hK4⟩
    exact (kharitonov4_two l u hlu h4).2 ⟨((hurwitzQuartic_iff h4).1 hK1).1, hK2, hK4⟩

/-! ### Applications -/

/-- **Quadrotor altitude** `m z̈ = T`, rotor lag `τ Ṫ = -T + T_cmd`, PID
`T_cmd = -(kp z + kd ż + ki ∫z)`: characteristic polynomial
`mτ s⁴ + m s³ + kd s² + kp s + ki`. Robust over payload `m ∈ [m₁,m₂]` and lag `τ ∈ [τ₁,τ₂]`
iff the heaviest/slowest corner satisfies `τ₂ kp² + m₂ ki < kd kp`. -/
theorem quadrotor_pid_robust {m₁ m₂ τ₁ τ₂ kp ki kd : ℝ} (hm : 0 < m₁) (hm' : m₁ ≤ m₂)
    (hτ : 0 < τ₁) (hτ' : τ₁ ≤ τ₂) :
    (∀ m ∈ Set.Icc m₁ m₂, ∀ τ ∈ Set.Icc τ₁ τ₂, HurwitzQuartic ki kp kd m (m * τ)) ↔
      0 < ki ∧ 0 < kp ∧ 0 < kd ∧ τ₂ * kp ^ 2 + m₂ * ki < kd * kp := by
  constructor
  · intro h
    obtain ⟨h0, h1, h2, -, hR⟩ :=
      (hurwitzQuartic_iff (by nlinarith)).1 (h m₂ ⟨hm', le_rfl⟩ τ₂ ⟨hτ', le_rfl⟩)
    refine ⟨h0, h1, h2, ?_⟩
    have hm2 : 0 < m₂ := by linarith
    nlinarith
  · rintro ⟨h0, h1, h2, hR⟩ m ⟨hm1, hm2⟩ τ ⟨hτ1, hτ2⟩
    have hm0 : 0 < m := by linarith
    rw [hurwitzQuartic_iff (by nlinarith)]
    refine ⟨h0, h1, h2, hm0, ?_⟩
    have : τ * kp ^ 2 + m * ki < kd * kp := by
      nlinarith [mul_le_mul_of_nonneg_right hτ2 (sq_nonneg kp), mul_le_mul_of_nonneg_right hm2 h0.le]
    nlinarith [mul_lt_mul_of_pos_left this hm0]

/-- Concrete quadrotor: `m ∈ [0.5, 1.5]` kg, rotor lag `τ ∈ [20, 50]` ms, `kp = 10`, `kd = 6`.
Robustly stable for `ki = 36` ... -/
example : ∀ m ∈ Set.Icc (0.5 : ℝ) 1.5, ∀ τ ∈ Set.Icc (0.02 : ℝ) 0.05,
    HurwitzQuartic 36 10 6 m (m * τ) :=
  (quadrotor_pid_robust (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- ... but not for `ki = 37` (exact threshold `110/3 ≈ 36.67`). -/
example : ¬ ∀ m ∈ Set.Icc (0.5 : ℝ) 1.5, ∀ τ ∈ Set.Icc (0.02 : ℝ) 0.05,
    HurwitzQuartic 37 10 6 m (m * τ) := by
  rw [quadrotor_pid_robust (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **Series-elastic actuator**, collocated PD on the motor: `J θ̈ₘ = τ - k(θₘ - θₗ)`,
`M θ̈ₗ = k(θₘ - θₗ)`, `τ = -kp θₘ - kd θ̇ₘ`. Characteristic polynomial
`JM s⁴ + kd M s³ + (Jk + M(kp+k)) s² + kd k s + k kp`. The Hurwitz determinant collapses to
`kd² M² k² > 0`, so it is stable for **every** motor inertia, load and spring stiffness
iff `kp, kd > 0` (passivity of collocated control). -/
theorem sea_pd_hurwitz_iff {J M k kp kd : ℝ} (hJ : 0 < J) (hM : 0 < M) (hk : 0 < k) :
    HurwitzQuartic (k * kp) (kd * k) (J * k + M * (kp + k)) (kd * M) (J * M) ↔
      0 < kp ∧ 0 < kd := by
  rw [hurwitzQuartic_iff (by positivity)]
  constructor
  · rintro ⟨h0, h1, -, -, -⟩
    exact ⟨pos_of_mul_pos_right h0 hk.le, pos_of_mul_pos_left h1 hk.le⟩
  · rintro ⟨hp, hd⟩
    refine ⟨by positivity, by positivity, by positivity, by positivity, ?_⟩
    have : kd * M * (J * k + M * (kp + k)) * (kd * k) - (J * M * (kd * k) ^ 2 + k * kp * (kd * M) ^ 2)
        = kd ^ 2 * M ^ 2 * k ^ 2 := by ring
    nlinarith [pow_pos (mul_pos (mul_pos hd hM) hk) 2]

end ControlsLean.Controls
