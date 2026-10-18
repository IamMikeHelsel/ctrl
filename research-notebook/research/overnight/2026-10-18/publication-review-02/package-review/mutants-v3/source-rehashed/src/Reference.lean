import RationalGuard

open Set
noncomputable section
namespace RobotMotion

def response (f : ℝ → ℝ) (h : ℝ) (es : List Event) (t : ℝ) : ℝ :=
  (es.map (fun e => e.2 * f ((t-e.1)/h))).sum

def position (g0 h : ℝ) (es : List Event) (t : ℝ) : ℝ := g0 + response F0 h es t
def velocity (h : ℝ) (es : List Event) (t : ℝ) : ℝ := response F1 h es t / h
def acceleration (h : ℝ) (es : List Event) (t : ℝ) : ℝ := response F2 h es t / h^2

lemma response_deriv (f df : ℝ → ℝ) (hf : ∀ z, HasDerivAt f (df z) z)
    (h : ℝ) (es : List Event) (t : ℝ) :
    HasDerivAt (response f h es) (response df h es t / h) t := by
  induction es with
  | nil =>
    change HasDerivAt (fun _ : ℝ => (0:ℝ)) (0/h) t
    rw [zero_div]
    exact hasDerivAt_const t 0
  | cons e es ih =>
    have he := ((hf ((t-e.1)/h)).comp t
      (((hasDerivAt_id t).sub_const e.1).div_const h)).const_mul e.2
    convert he.add ih using 1
    · funext u; simp [response]
    · simp [response]; ring

lemma max_scaled {h : ℝ} (hh : 0 < h) (a t : ℝ) :
    max ((t-a)/h) 0 = H a t / h := by
  by_cases ht : 0 ≤ t-a
  · rw [max_eq_left (div_nonneg ht hh.le),H,max_eq_left ht]
  · have hneg : t-a ≤ 0 := le_of_lt (lt_of_not_ge ht)
    rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg hneg hh.le),H,max_eq_right hneg,zero_div]

lemma scaled_shift {h : ℝ} (hh : 0 < h) (a t m : ℝ) :
    (t-a)/h-m = (t-(a+m*h))/h := by field_simp; ring

lemma eventJerk_eq {h : ℝ} (hh : 0 < h) (e : Event) (t : ℝ) :
    eventJerk h e t = e.2 * F3 ((t-e.1)/h) / h^3 := by
  simp only [F3,P,pow_one,scaled_shift hh,max_scaled hh]
  simp only [eventJerk]
  field_simp <;> ring

lemma jerk_eq_response {h : ℝ} (hh : 0 < h) (es : List Event) (t : ℝ) :
    jerk h es t = response F3 h es t / h^3 := by
  induction es with
  | nil => simp [jerk,response]
  | cons e es ih =>
    simp only [jerk,response,List.map_cons,List.sum_cons] at *
    rw [eventJerk_eq hh,ih]
    ring

theorem position_deriv (g0 h : ℝ) (es : List Event) (t : ℝ) :
    HasDerivAt (position g0 h es) (velocity h es t) t := by
  exact (response_deriv F0 F1 F0_deriv h es t).const_add g0

theorem velocity_deriv (h : ℝ) (es : List Event) (t : ℝ) :
    HasDerivAt (velocity h es) (acceleration h es t) t := by
  convert (response_deriv F1 F2 F1_deriv h es t).div_const h using 1
  · rfl
  · dsimp [acceleration]; ring

theorem acceleration_deriv {h : ℝ} (hh : 0 < h) (es : List Event) (t : ℝ) :
    HasDerivAt (acceleration h es) (jerk h es t) t := by
  convert (response_deriv F2 F3 F2_deriv h es t).div_const (h^2) using 1
  · rfl
  · rw [jerk_eq_response hh]; ring

lemma response_continuous (f : ℝ → ℝ) (hf : Continuous f) (h : ℝ) (es : List Event) :
    Continuous (response f h es) := by
  induction es with
  | nil =>
    change Continuous (fun _ : ℝ => (0:ℝ))
    exact continuous_const
  | cons e es ih =>
    change Continuous (fun t => e.2 * f ((t-e.1)/h) + response f h es t)
    exact (continuous_const.mul (hf.comp ((continuous_id.sub continuous_const).div_const h))).add ih

theorem position_continuous (g0 h : ℝ) (es : List Event) : Continuous (position g0 h es) :=
  continuous_const.add (response_continuous F0 F0_continuous h es)
theorem velocity_continuous (h : ℝ) (es : List Event) : Continuous (velocity h es) :=
  (response_continuous F1 F1_continuous h es).div_const h
theorem acceleration_continuous (h : ℝ) (es : List Event) : Continuous (acceleration h es) :=
  (response_continuous F2 F2_continuous h es).div_const (h^2)
theorem jerk_continuous {h : ℝ} (hh : 0 < h) (es : List Event) : Continuous (jerk h es) := by
  have heq : jerk h es = fun t => response F3 h es t / h^3 := funext (jerk_eq_response hh es)
  rw [heq]
  exact (response_continuous F3 F3_continuous h es).div_const (h^3)

lemma response_append (f : ℝ → ℝ) (h : ℝ) (es fs : List Event) (t : ℝ) :
    response f h (es++fs) t = response f h es t + response f h fs t := by simp [response]
lemma jerk_append (h : ℝ) (es fs : List Event) (t : ℝ) :
    jerk h (es++fs) t = jerk h es t + jerk h fs t := by simp [jerk]

/-- A newly committed event starts at tau, and preserves every point through c <= tau. -/
theorem prefix_preservation {h c tau : ℝ} (hh : 0 < h) (hct : c ≤ tau)
    (g0 delta : ℝ) (es : List Event) {t : ℝ} (ht : t ≤ c) :
    position g0 h (es++[(tau,delta)]) t = position g0 h es t ∧
    velocity h (es++[(tau,delta)]) t = velocity h es t ∧
    acceleration h (es++[(tau,delta)]) t = acceleration h es t ∧
    jerk h (es++[(tau,delta)]) t = jerk h es t := by
  have hz : (t-tau)/h ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le
  obtain ⟨h0,h1,h2,h3⟩ := left_tail hz
  simp [position,velocity,acceleration,response_append,response,h0,h1,h2,
    jerk_eq_response hh,h3]

lemma response_rest (f : ℝ → ℝ) (v : ℝ) (hf : ∀ z, 4 ≤ z → f z = v)
    {h T t : ℝ} (hh : 0 < h) (es : List Event)
    (hT : ∀ e ∈ es, e.1 ≤ T) (ht : T+4*h ≤ t) :
    response f h es t = (es.map Prod.snd).sum * v := by
  induction es with
  | nil => simp [response]
  | cons e es ih =>
    have he : 4 ≤ (t-e.1)/h := (le_div_iff₀ hh).mpr (by linarith [hT e (by simp)])
    have hs := ih (fun a ha => hT a (by simp [ha]))
    simp only [response,List.map_cons,List.sum_cons] at *
    rw [hf _ he,hs]
    ring

/-- Every accepted event, including queued future events, contributes to the final target. -/
theorem final_rest {h T t : ℝ} (hh : 0 < h) (g0 : ℝ) (es : List Event)
    (hT : ∀ e ∈ es, e.1 ≤ T) (ht : T+4*h ≤ t) :
    position g0 h es t = g0+(es.map Prod.snd).sum ∧ velocity h es t = 0 ∧
    acceleration h es t = 0 ∧ jerk h es t = 0 := by
  have h0 := response_rest F0 1 (fun _ hz => (right_tail hz).1) hh es hT ht
  have h1 := response_rest F1 0 (fun _ hz => (right_tail hz).2.1) hh es hT ht
  have h2 := response_rest F2 0 (fun _ hz => (right_tail hz).2.2.1) hh es hT ht
  have h3 := response_rest F3 0 (fun _ hz => (right_tail hz).2.2.2) hh es hT ht
  simp [position,velocity,acceleration,jerk_eq_response hh,h0,h1,h2,h3]

/-- The complete reference jet through jerk. -/
def referenceJet (g0 h : ℝ) (es : List Event) (t : ℝ) : Fin 4 → ℝ :=
  ![position g0 h es t,velocity h es t,acceleration h es t,jerk h es t]

lemma prefix_jet {h c tau : ℝ} (hh : 0 < h) (hct : c ≤ tau)
    (g0 delta : ℝ) (es : List Event) {t : ℝ} (ht : t ≤ c) :
    referenceJet g0 h (es++[(tau,delta)]) t = referenceJet g0 h es t := by
  obtain ⟨h0,h1,h2,h3⟩ := prefix_preservation hh hct g0 delta es ht
  funext i
  fin_cases i <;> simp [referenceJet,h0,h1,h2,h3]

end RobotMotion
