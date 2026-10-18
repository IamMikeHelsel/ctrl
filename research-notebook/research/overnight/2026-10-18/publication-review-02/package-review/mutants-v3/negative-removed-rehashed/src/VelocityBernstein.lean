import SuccessorGuard

open Set
namespace RobotMotion.VelocityAdmission
open AccelerationAdmission

/-- Rational velocity of the same retained four-box reference. -/
def qEventVelocity (h : ℚ) (e : QEvent) (t : ℚ) : ℚ :=
  e.2 / (6*h^4) * (qH e.1 t ^ 3 - 4*qH (e.1+h) t ^ 3 +
    6*qH (e.1+2*h) t ^ 3 - 4*qH (e.1+3*h) t ^ 3 + qH (e.1+4*h) t ^ 3)

def qVelocity (h : ℚ) (es : List QEvent) (t : ℚ) : ℚ :=
  (es.map (fun e => qEventVelocity h e t)).sum

noncomputable section

lemma event_velocity_eq {h : ℝ} (hh : 0 < h) (e : Event) (t : ℝ) :
    e.2 * F1 ((t-e.1)/h) / h =
      e.2 / (6*h^4) * (H e.1 t ^ 3 - 4*H (e.1+h) t ^ 3 +
      6*H (e.1+2*h) t ^ 3 - 4*H (e.1+3*h) t ^ 3 + H (e.1+4*h) t ^ 3) := by
  simp only [F1,P,scaled_shift hh,max_scaled hh]
  field_simp <;> ring

lemma cast_qVelocity {h : ℚ} (hh : 0 < h) (es : List QEvent) (t : ℚ) :
    ((qVelocity h es t : ℚ):ℝ) = velocity (h:ℝ) (realEvents es) (t:ℝ) := by
  induction es with
  | nil => simp [qVelocity,velocity,response,realEvents]
  | cons e es ih =>
    have he := event_velocity_eq (by exact_mod_cast hh : (0:ℝ)<h) (realEvent e) (t:ℝ)
    simp [qEventVelocity,realEvent,cast_qH] at he
    simp only [qVelocity,List.map_cons,List.sum_cons,Rat.cast_add] at *
    rw [ih]
    simp only [velocity,realEvents,List.map_cons,response,List.map_cons,List.sum_cons]
    simp only [qEventVelocity,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_add,
      Rat.cast_pow,Rat.cast_ofNat,cast_qH]
    dsimp [realEvent] at he ⊢
    rw [add_div]
    linarith

/-- Cubic Bernstein polynomial in four scalar coefficients. -/
def blend (u b0 b1 b2 b3 : ℝ) : ℝ :=
  (1-u)^3*b0 + 3*u*(1-u)^2*b1 + 3*u^2*(1-u)*b2 + u^3*b3

/-- Hermite data expressed as Bernstein coefficients on a cell of width d. -/
def cellBlend (u d vL aL vR aR : ℝ) : ℝ :=
  blend u vL (vL+d*aL/3) (vR-d*aR/3) vR

lemma H_cube_blend {a L R t : ℝ} (hLR : L < R) (hLt : L ≤ t) (htR : t ≤ R)
    (ha : a ≤ L ∨ R ≤ a) :
    H a t ^ 3 = cellBlend ((t-L)/(R-L)) (R-L)
      (H a L ^ 3) (3*H a L ^ 2) (H a R ^ 3) (3*H a R ^ 2) := by
  have hn : R-L ≠ 0 := sub_ne_zero.mpr (ne_of_gt hLR)
  rcases ha with ha | ha
  · simp only [H,max_eq_left (by linarith : 0 ≤ t-a),
      max_eq_left (by linarith : 0 ≤ L-a),max_eq_left (by linarith : 0 ≤ R-a),
      cellBlend,blend]
    field_simp
    <;> ring
  · simp only [H,max_eq_right (by linarith : t-a ≤ 0),
      max_eq_right (by linarith : L-a ≤ 0),max_eq_right (by linarith : R-a ≤ 0),
      cellBlend,blend]
    ring

lemma event_velocity_blend {h L R t : ℝ} (hh : 0 < h) (e : Event)
    (hLR : L < R) (hLt : L ≤ t) (htR : t ≤ R)
    (hroot : ∀ a ∈ eventRoots h e, a ≤ L ∨ R ≤ a) :
    e.2 * F1 ((t-e.1)/h) / h =
      cellBlend ((t-L)/(R-L)) (R-L)
        (e.2 * F1 ((L-e.1)/h) / h) (e.2 * F2 ((L-e.1)/h) / h^2)
        (e.2 * F1 ((R-e.1)/h) / h) (e.2 * F2 ((R-e.1)/h) / h^2) := by
  have h0 := H_cube_blend hLR hLt htR (hroot e.1 (by simp [eventRoots]))
  have h1 := H_cube_blend hLR hLt htR (hroot (e.1+h) (by simp [eventRoots]))
  have h2 := H_cube_blend hLR hLt htR (hroot (e.1+2*h) (by simp [eventRoots]))
  have h3 := H_cube_blend hLR hLt htR (hroot (e.1+3*h) (by simp [eventRoots]))
  have h4 := H_cube_blend hLR hLt htR (hroot (e.1+4*h) (by simp [eventRoots]))
  rw [event_velocity_eq hh, event_velocity_eq hh, event_velocity_eq hh,
    event_acceleration_eq hh, event_acceleration_eq hh]
  dsimp [cellBlend,blend] at *
  linear_combination (e.2/(6*h^4))*h0 - 4*(e.2/(6*h^4))*h1 +
    6*(e.2/(6*h^4))*h2 - 4*(e.2/(6*h^4))*h3 + (e.2/(6*h^4))*h4

/-- The actual reference velocity is the cubic determined by its endpoint
velocity and acceleration, on each cell with no event knot in its interior. -/
theorem velocity_blend {h L R t : ℝ} (hh : 0 < h) (es : List Event)
    (hLR : L < R) (hLt : L ≤ t) (htR : t ≤ R)
    (hroot : ∀ a ∈ roots h es, a ≤ L ∨ R ≤ a) :
    velocity h es t = cellBlend ((t-L)/(R-L)) (R-L)
      (velocity h es L) (acceleration h es L)
      (velocity h es R) (acceleration h es R) := by
  induction es with
  | nil => simp [velocity,acceleration,response,cellBlend,blend]
  | cons e es ih =>
    have he := event_velocity_blend hh e hLR hLt htR
      (fun a ha => hroot a (by change a ∈ eventRoots h e ++ roots h es; exact List.mem_append_left _ ha))
    have hs := ih (fun a ha => hroot a (by simp [roots] at ha ⊢; exact Or.inr ha))
    simp only [velocity,acceleration,response,List.map_cons,List.sum_cons,add_div] at *
    dsimp [cellBlend,blend] at *
    linear_combination he + hs

/-- Bernstein weights are nonnegative and sum to one on the closed cell. -/
lemma blend_abs_le {u b0 b1 b2 b3 V : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h0 : |b0| ≤ V) (h1 : |b1| ≤ V) (h2 : |b2| ≤ V) (h3 : |b3| ≤ V) :
    |blend u b0 b1 b2 b3| ≤ V := by
  have hw0 : 0 ≤ (1-u)^3 := pow_nonneg (sub_nonneg.mpr hu1) _
  have hw1 : 0 ≤ 3*u*(1-u)^2 := by positivity
  have hw2 : 0 ≤ 3*u^2*(1-u) := by positivity
  have hw3 : 0 ≤ u^3 := pow_nonneg hu0 _
  have hw : (1-u)^3 + 3*u*(1-u)^2 + 3*u^2*(1-u) + u^3 = 1 := by ring
  have h0a := mul_le_mul_of_nonneg_left (abs_le.mp h0).1 hw0
  have h0b := mul_le_mul_of_nonneg_left (abs_le.mp h0).2 hw0
  have h1a := mul_le_mul_of_nonneg_left (abs_le.mp h1).1 hw1
  have h1b := mul_le_mul_of_nonneg_left (abs_le.mp h1).2 hw1
  have h2a := mul_le_mul_of_nonneg_left (abs_le.mp h2).1 hw2
  have h2b := mul_le_mul_of_nonneg_left (abs_le.mp h2).2 hw2
  have h3a := mul_le_mul_of_nonneg_left (abs_le.mp h3).1 hw3
  have h3b := mul_le_mul_of_nonneg_left (abs_le.mp h3).2 hw3
  have hwV := congrArg (fun x => x*V) hw
  unfold blend
  apply abs_le.mpr
  constructor <;> nlinarith only [h0a,h0b,h1a,h1b,h2a,h2b,h3a,h3b,hwV]

lemma velocity_cell_bound {h L R t V : ℝ} (hh : 0 < h) (es : List Event)
    (hLR : L < R) (hLt : L ≤ t) (htR : t ≤ R)
    (hroot : ∀ a ∈ roots h es, a ≤ L ∨ R ≤ a)
    (h0 : |velocity h es L| ≤ V)
    (h1 : |velocity h es L+(R-L)*acceleration h es L/3| ≤ V)
    (h2 : |velocity h es R-(R-L)*acceleration h es R/3| ≤ V)
    (h3 : |velocity h es R| ≤ V) : |velocity h es t| ≤ V := by
  rw [velocity_blend hh es hLR hLt htR hroot]
  exact blend_abs_le (div_nonneg (sub_nonneg.mpr hLt) (sub_nonneg.mpr hLR.le))
    ((div_le_one (sub_pos.mpr hLR)).mpr (by linarith)) h0 h1 h2 h3

lemma velocity_tail {h t : ℝ} (hh : 0 < h) (es : List Event)
    (ht : ∀ a ∈ roots h es, a ≤ t) : velocity h es t = 0 := by
  have hz : response F1 h es t = 0 := by
    apply List.sum_eq_zero
    intro v hv
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hv
    have he4 := ht (e.1+4*h) (List.mem_flatMap.mpr ⟨e,he,by simp [eventRoots]⟩)
    have hz : 4 ≤ (t-e.1)/h := (le_div_iff₀ hh).mpr (by linarith)
    simp [(right_tail hz).2.1]
  simp [velocity,hz]

end
end RobotMotion.VelocityAdmission
