import AccelerationFixtures

open Set
noncomputable section
namespace RobotMotion.AccelerationAdmission

/-- Global velocity-kernel range; this is a reference property. -/
lemma F1_range (z : ℝ) : 0 ≤ F1 z ∧ F1 z ≤ 2/3 := by
  by_cases h0 : z ≤ 0
  · rw [(left_tail h0).2.1]; norm_num
  by_cases h4 : 4 ≤ z
  · rw [(right_tail h4).2.1]; norm_num
  have hz0 : 0 ≤ z := (lt_of_not_ge h0).le
  have hz4 : z ≤ 4 := (lt_of_not_ge h4).le
  by_cases h1 : z ≤ 1
  · have he : F1 z = z^3/6 := by
      simp [F1,P,max_eq_left hz0,max_eq_right (by linarith : z-1≤0),
        max_eq_right (by linarith : z-2≤0),max_eq_right (by linarith : z-3≤0),
        max_eq_right (by linarith : z-4≤0)]
    rw [he]
    constructor
    · positivity
    · have hp : z^3 ≤ 1 := pow_le_one₀ hz0 h1
      nlinarith
  have hz1 : 1 ≤ z := (lt_of_not_ge h1).le
  by_cases h2 : z ≤ 2
  · have he : F1 z = (z^3-4*(z-1)^3)/6 := by
      simp [F1,P,max_eq_left hz0,max_eq_left (by linarith : 0≤z-1),
        max_eq_right (by linarith : z-2≤0),max_eq_right (by linarith : z-3≤0),
        max_eq_right (by linarith : z-4≤0)]
    rw [he]
    have hp := mul_nonneg (sq_nonneg (z-1)) (by linarith : 0≤2-z)
    have hq := mul_nonneg hz0 (sq_nonneg (z-2))
    constructor <;> nlinarith
  have hz2 : 2 ≤ z := (lt_of_not_ge h2).le
  by_cases h3 : z ≤ 3
  · have he : F1 z = (z^3-4*(z-1)^3+6*(z-2)^3)/6 := by
      simp [F1,P,max_eq_left hz0,max_eq_left (by linarith : 0≤z-1),
        max_eq_left (by linarith : 0≤z-2),max_eq_right (by linarith : z-3≤0),
        max_eq_right (by linarith : z-4≤0)]
    rw [he]
    have hp := mul_nonneg (sq_nonneg (3-z)) (by linarith : 0≤z-2)
    have hq := mul_nonneg (by linarith : 0≤4-z) (sq_nonneg (z-2))
    constructor <;> nlinarith
  have hz3 : 3 ≤ z := (lt_of_not_ge h3).le
  have he : F1 z = (4-z)^3/6 := by
    simp only [F1,P,max_eq_left hz0,max_eq_left (by linarith : 0≤z-1),
      max_eq_left (by linarith : 0≤z-2),max_eq_left (by linarith : 0≤z-3),
      max_eq_right (by linarith : z-4≤0),zero_pow (by norm_num : 3 ≠ 0)]
    ring
  rw [he]
  have hp : (4-z)^3 ≤ 1 := pow_le_one₀ (by linarith : 0≤4-z) (by linarith : 4-z≤1)
  have hq := pow_nonneg (by linarith : 0≤4-z) 3
  constructor <;> nlinarith

/-- Any equal-and-opposite two-event reference has this velocity bound.
The theorem does not assert that all such references meet acceleration or jerk limits. -/
lemma equal_return_velocity_bound {h d : ℝ} (hh : 0 < h) (hd : 0 ≤ d)
    (L R t : ℝ) : |velocity h [(L,d),(R,-d)] t| ≤ 2*d/(3*h) := by
  obtain ⟨hL0,hL1⟩ := F1_range ((t-L)/h)
  obtain ⟨hR0,hR1⟩ := F1_range ((t-R)/h)
  have hv : velocity h [(L,d),(R,-d)] t = d*(F1 ((t-L)/h)-F1 ((t-R)/h))/h := by
    simp [velocity,response]; ring
  rw [hv,abs_div,abs_of_pos hh]
  apply (div_le_iff₀ hh).mpr
  have he : 2*d/(3*h)*h = 2*d/3 := by field_simp <;> ring
  rw [he]
  have ha : |F1 ((t-L)/h)-F1 ((t-R)/h)| ≤ 2/3 := by
    apply abs_le.mpr; constructor <;> linarith
  rw [abs_mul,abs_of_nonneg hd]
  nlinarith [mul_le_mul_of_nonneg_left ha hd]

/-- A new proposal keeps the old first event and defers only the return by 100 ms.
It is a new candidate, not a replacement of the frozen failed experiment. -/
theorem deferred_return_reference_contract :
    (∀ t : ℝ, 0 ≤ t → |acceleration (1/5) (realEvents deferredReturn) t| ≤ 1/2) ∧
    (∀ t : ℝ, 0 ≤ t → |jerk (1/5) (realEvents deferredReturn) t| ≤ 15/2) ∧
    (∀ t : ℝ, |velocity (1/5) (realEvents deferredReturn) t| ≤ 1/15) ∧
    (∀ t : ℝ, 71/50 ≤ t → position 0 (1/5) (realEvents deferredReturn) t = 0 ∧
      velocity (1/5) (realEvents deferredReturn) t = 0 ∧
      acceleration (1/5) (realEvents deferredReturn) t = 0 ∧
      jerk (1/5) (realEvents deferredReturn) t = 0) := by
  constructor
  · simpa using ((checkAcceleration_real_iff (1/5) (1/2) 0 deferredReturn).mp deferred_return_acceleration).2.2
  constructor
  · simpa using ((check_real_iff (1/5) (15/2) 0 deferredReturn).mp deferred_return_jerk).2.2
  constructor
  · intro t
    have hv := equal_return_velocity_bound (h:=1/5) (d:=1/50) (by norm_num) (by norm_num) (11/50) (31/50) t
    norm_num [realEvents,realEvent,deferredReturn] at hv ⊢
    exact hv
  · intro t ht
    have hf := final_rest (h:=1/5) (T:=31/50) (t:=t) (by norm_num) 0 (realEvents deferredReturn)
      (by intro e he; simp [deferredReturn,realEvents,realEvent] at he; rcases he with rfl | rfl <;> norm_num)
      (by linarith)
    norm_num [deferredReturn,realEvents,realEvent] at hf ⊢
    exact hf

/-- The delayed event cannot rewrite the already-issued reference jet. -/
theorem deferred_return_preserves_prefix (t : ℝ) (ht : t ≤ 31/50) :
    referenceJet 0 (1/5) (realEvents deferredReturn) t =
      referenceJet 0 (1/5) [(11/50,1/50)] t := by
  have hp := prefix_jet (h:=1/5) (c:=31/50) (tau:=31/50) (by norm_num) le_rfl 0 (-1/50) [(11/50,1/50)] ht
  norm_num [deferredReturn,realEvents,realEvent] at hp ⊢
  exact hp

/-- The reference settles 280 ms before the unchanged generous deadline. -/
theorem deferred_return_deadline : (71/50:ℝ) < 17/10 := by norm_num

end RobotMotion.AccelerationAdmission
