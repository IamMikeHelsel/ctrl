module
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Topology.Piecewise
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace LeanControls.SmoothReplan
open Set
open scoped Topology

/-- A scalar constant-jerk segment, in physical seconds. -/
structure State where
  q : ℝ
  v : ℝ
  a : ℝ

def position (z : State) (j t : ℝ) : ℝ := z.q + z.v*t + z.a*t^2/2 + j*t^3/6
def velocity (z : State) (j t : ℝ) : ℝ := z.v + z.a*t + j*t^2/2
def acceleration (z : State) (j t : ℝ) : ℝ := z.a + j*t

def advance (z : State) (j h : ℝ) : State :=
  ⟨position z j h, velocity z j h, acceleration z j h⟩

theorem segment_initial (z : State) (j : ℝ) :
    position z j 0 = z.q ∧ velocity z j 0 = z.v ∧ acceleration z j 0 = z.a := by
  simp [position, velocity, acceleration]

theorem segment_position_derivative (z : State) (j t : ℝ) :
    HasDerivAt (position z j) (velocity z j t) t := by
  have h : HasDerivAt (fun s : ℝ => z.q + z.v*s + z.a*s^2/2 + j*s^3/6)
      (0 + z.v*1 + (z.a*(2*t^1*1))/2 + (j*(3*t^2*1))/6) t := by
    exact HasDerivAt.add
      (HasDerivAt.add
        (HasDerivAt.add (hasDerivAt_const t z.q) ((hasDerivAt_id t).const_mul z.v))
        (((hasDerivAt_id t).pow 2).const_mul z.a |>.div_const 2))
      (((hasDerivAt_id t).pow 3).const_mul j |>.div_const 6)
  change HasDerivAt (fun s : ℝ => z.q + z.v*s + z.a*s^2/2 + j*s^3/6) (z.v+z.a*t+j*t^2/2) t
  convert h using 1; ring

theorem segment_velocity_derivative (z : State) (j t : ℝ) :
    HasDerivAt (velocity z j) (acceleration z j t) t := by
  have h : HasDerivAt (fun s : ℝ => z.v + z.a*s + j*s^2/2)
      (0+z.a*1+j*(2*t^1*1)/2) t := by
    exact HasDerivAt.add
      (HasDerivAt.add (hasDerivAt_const t z.v) ((hasDerivAt_id t).const_mul z.a))
      (((hasDerivAt_id t).pow 2).const_mul j |>.div_const 2)
  change HasDerivAt (fun s : ℝ => z.v + z.a*s + j*s^2/2) (z.a+j*t) t
  convert h using 1; ring

theorem segment_acceleration_derivative (z : State) (j t : ℝ) :
    HasDerivAt (acceleration z j) j t := by
  have h : HasDerivAt (fun s : ℝ => z.a+j*s) (0+j*1) t :=
    HasDerivAt.add (hasDerivAt_const t z.a) ((hasDerivAt_id t).const_mul j)
  change HasDerivAt (fun s : ℝ => z.a+j*s) j t
  convert h using 1; ring

/-- A new segment starts at the executed state, including acceleration. -/
theorem matched_switch (z : State) (jOld jNew h : ℝ) :
    position (advance z jOld h) jNew 0 = position z jOld h ∧
    velocity (advance z jOld h) jNew 0 = velocity z jOld h ∧
    acceleration (advance z jOld h) jNew 0 = acceleration z jOld h := by
  simpa [advance] using segment_initial (advance z jOld h) jNew

def lerp (u x y : ℝ) := (1-u)*x+u*y
def bezier2 (u p0 p1 p2 : ℝ) := lerp u (lerp u p0 p1) (lerp u p1 p2)
def bezier3 (u p0 p1 p2 p3 : ℝ) :=
  lerp u (bezier2 u p0 p1 p2) (bezier2 u p1 p2 p3)

theorem lerp_mem_Icc {u L U x y : ℝ} (hu : u ∈ Icc 0 1)
    (hx : x ∈ Icc L U) (hy : y ∈ Icc L U) : lerp u x y ∈ Icc L U := by
  dsimp [lerp]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hx.1),
      mul_nonneg hu.1 (sub_nonneg.mpr hy.1)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hx.2),
      mul_nonneg hu.1 (sub_nonneg.mpr hy.2)]

theorem bezier2_mem_Icc {u L U p0 p1 p2 : ℝ} (hu : u ∈ Icc 0 1)
    (h0 : p0 ∈ Icc L U) (h1 : p1 ∈ Icc L U) (h2 : p2 ∈ Icc L U) :
    bezier2 u p0 p1 p2 ∈ Icc L U :=
  lerp_mem_Icc hu (lerp_mem_Icc hu h0 h1) (lerp_mem_Icc hu h1 h2)

theorem bezier3_mem_Icc {u L U p0 p1 p2 p3 : ℝ} (hu : u ∈ Icc 0 1)
    (h0 : p0 ∈ Icc L U) (h1 : p1 ∈ Icc L U) (h2 : p2 ∈ Icc L U)
    (h3 : p3 ∈ Icc L U) : bezier3 u p0 p1 p2 p3 ∈ Icc L U :=
  lerp_mem_Icc hu (bezier2_mem_Icc hu h0 h1 h2) (bezier2_mem_Icc hu h1 h2 h3)

/-- Finite control-point conditions for an entire continuous-time segment.
They are sufficient; failing them does not prove a trajectory unsafe. -/
structure Admission (z : State) (j h L U V A J : ℝ) : Prop where
  duration : 0 < h
  jerk : |j| ≤ J
  q0 : z.q ∈ Icc L U
  q1 : z.q + z.v*h/3 ∈ Icc L U
  q2 : z.q + 2*z.v*h/3 + z.a*h^2/6 ∈ Icc L U
  q3 : position z j h ∈ Icc L U
  v0 : z.v ∈ Icc (-V) V
  v1 : z.v + z.a*h/2 ∈ Icc (-V) V
  v2 : velocity z j h ∈ Icc (-V) V
  a0 : z.a ∈ Icc (-A) A
  a1 : acceleration z j h ∈ Icc (-A) A

theorem admission_all_time {z : State} {j h L U V A J t : ℝ}
    (hc : Admission z j h L U V A J) (ht : t ∈ Icc 0 h) :
    position z j t ∈ Icc L U ∧ velocity z j t ∈ Icc (-V) V ∧
    acceleration z j t ∈ Icc (-A) A ∧ |j| ≤ J := by
  have hh : h ≠ 0 := ne_of_gt hc.duration
  have hu : t/h ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg ht.1 hc.duration.le, (div_le_one hc.duration).mpr ht.2⟩
  have hq := bezier3_mem_Icc hu hc.q0 hc.q1 hc.q2 hc.q3
  have hv := bezier2_mem_Icc hu hc.v0 hc.v1 hc.v2
  have ha := lerp_mem_Icc hu hc.a0 hc.a1
  have eqQ : bezier3 (t/h) z.q (z.q+z.v*h/3)
      (z.q+2*z.v*h/3+z.a*h^2/6) (position z j h) = position z j t := by
    dsimp [bezier3, bezier2, lerp, position]; field_simp; ring
  have eqV : bezier2 (t/h) z.v (z.v+z.a*h/2) (velocity z j h) = velocity z j t := by
    dsimp [bezier2, lerp, velocity]; field_simp; ring
  have eqA : lerp (t/h) z.a (acceleration z j h) = acceleration z j t := by
    dsimp [lerp, acceleration]; field_simp; ring
  exact ⟨eqQ ▸ hq, eqV ▸ hv, eqA ▸ ha, hc.jerk⟩

/-- Planning may propose any jerk, but the admission check is on the executed jerk. -/
def JerkLimited (J : ℝ) (a : ℝ → ℝ) : Prop :=
  ∀ s t : ℝ, s ≤ t → |a t-a s| ≤ J*(t-s)

def splice (c : ℝ) (old new : ℝ → ℝ) (t : ℝ) := if t ≤ c then old t else new t

theorem segment_jerk_limited {z : State} {j J : ℝ} (hj : |j| ≤ J) :
    JerkLimited J (acceleration z j) := by
  intro s t hst
  have eq : acceleration z j t - acceleration z j s = j*(t-s) := by
    simp [acceleration]; ring
  rw [eq, abs_mul, abs_of_nonneg (sub_nonneg.mpr hst)]
  exact mul_le_mul_of_nonneg_right hj (sub_nonneg.mpr hst)

/-- Matching acceleration makes the jerk bound independent of switch frequency.
This bounds jerk in the Lipschitz sense and permits jumps in jerk itself. -/
theorem splice_jerk_limited {J c : ℝ} {old new : ℝ → ℝ}
    (ho : JerkLimited J old) (hn : JerkLimited J new) (hm : old c = new c) :
    JerkLimited J (splice c old new) := by
  intro s t hst
  by_cases hs : s ≤ c
  · by_cases ht : t ≤ c
    · simpa [splice, hs, ht] using ho s t hst
    · have hsc := ho s c hs
      have hct := hn c t (le_of_not_ge ht)
      have heq : new t - old s = (new t-new c)+(old c-old s) := by rw [hm]; ring
      simp only [splice, hs, ht, ite_true, ite_false]
      rw [heq]
      calc
        |(new t-new c)+(old c-old s)| ≤ |new t-new c|+|old c-old s| := abs_add_le _ _
        _ ≤ J*(t-c)+J*(c-s) := add_le_add hct hsc
        _ = J*(t-s) := by ring
  · have ht : ¬t ≤ c := by intro h; exact hs (hst.trans h)
    simpa [splice, hs, ht] using hn s t hst

/-- A finite replacement history. There is deliberately no minimum dwell premise. -/
inductive CertifiedHistory (J : ℝ) : (ℝ → ℝ) → Prop where
  | initial {a} : JerkLimited J a → CertifiedHistory J a
  | replace {old new} (c : ℝ) : CertifiedHistory J old → JerkLimited J new →
      old c = new c → CertifiedHistory J (splice c old new)

theorem finite_replans_preserve_jerk {J : ℝ} {a : ℝ → ℝ}
    (h : CertifiedHistory J a) : JerkLimited J a := by
  induction h with
  | initial h => exact h
  | replace c _ hn hm ih => exact splice_jerk_limited ih hn hm

/-- The committed past is unchanged by an admitted replacement. -/
theorem splice_keeps_prefix {c t : ℝ} {old new : ℝ → ℝ} (ht : t ≤ c) :
    splice c old new t = old t := by simp [splice, ht]

/-- A known position tracking error can be reserved before admission. -/
theorem tracking_tube {qActual qCommand L U e : ℝ}
    (hc : qCommand ∈ Icc (L+e) (U-e)) (he : |qActual-qCommand| ≤ e) :
    qActual ∈ Icc L U := by
  rcases abs_le.mp he with ⟨hl,hu⟩
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩


/-- Derivatives agree at the actual execution boundary, not at plan-generation time. -/
theorem splice_derivative_at_switch {c d : ℝ} {old new : ℝ → ℝ}
    (ho : HasDerivAt old d c) (hn : HasDerivAt new d c) (hm : old c = new c) :
    HasDerivAt (splice c old new) d c := by
  have hl : HasDerivWithinAt (splice c old new) d (Iic c) c := by
    apply ho.hasDerivWithinAt.congr
    · intro t ht; simp [splice, show t ≤ c from ht]
    · simp [splice]
  have hr : HasDerivWithinAt (splice c old new) d (Ici c) c := by
    apply hn.hasDerivWithinAt.congr
    · intro t ht
      by_cases htc : t ≤ c
      · have heq : t = c := le_antisymm htc ht
        subst t; simp [splice, hm]
      · simp [splice, htc]
    · simp [splice, hm]
  have hboth := hl.union hr
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hboth

theorem splice_continuous {c : ℝ} {old new : ℝ → ℝ}
    (ho : Continuous old) (hn : Continuous new) (hm : old c = new c) :
    Continuous (splice c old new) := by
  apply Continuous.if _ ho hn
  intro t ht
  have htc : t = c := by
    change t ∈ frontier (Iic c) at ht
    simpa only [frontier_Iic, mem_singleton_iff] using ht
  simpa [htc] using hm

/-- State matching preserves the derivative relation at every time, including the switch. -/
theorem splice_derivative_everywhere {c : ℝ} {old new oldD newD : ℝ → ℝ}
    (ho : ∀ t, HasDerivAt old (oldD t) t) (hn : ∀ t, HasDerivAt new (newD t) t)
    (hm : old c = new c) (hd : oldD c = newD c) :
    ∀ t, HasDerivAt (splice c old new) (splice c oldD newD t) t := by
  intro t
  rcases lt_trichotomy t c with h | rfl | h
  · have he : splice c old new =ᶠ[𝓝 t] old := by
      filter_upwards [eventually_lt_nhds h] with u hu
      simp [splice, hu.le]
    simpa [splice, h.le] using (ho t).congr_of_eventuallyEq he
  · have hn' : HasDerivAt new (oldD t) t := hd ▸ hn t
    simpa [splice] using splice_derivative_at_switch (ho t) hn' hm
  · have he : splice c old new =ᶠ[𝓝 t] new := by
      filter_upwards [eventually_gt_nhds h] with u hu
      simp [splice, not_le.mpr hu]
    simpa [splice, not_le.mpr h] using (hn t).congr_of_eventuallyEq he

/-- The usual C2 motion contract: q'=v, v'=a everywhere and a continuous.
No claim that jerk is continuous is made. -/
theorem splice_motion_contract {c : ℝ} {qO qN vO vN aO aN : ℝ → ℝ}
    (hqO : ∀ t, HasDerivAt qO (vO t) t) (hqN : ∀ t, HasDerivAt qN (vN t) t)
    (hvO : ∀ t, HasDerivAt vO (aO t) t) (hvN : ∀ t, HasDerivAt vN (aN t) t)
    (haO : Continuous aO) (haN : Continuous aN)
    (mq : qO c = qN c) (mv : vO c = vN c) (ma : aO c = aN c) :
    (∀ t, HasDerivAt (splice c qO qN) (splice c vO vN t) t) ∧
    (∀ t, HasDerivAt (splice c vO vN) (splice c aO aN t) t) ∧
    Continuous (splice c aO aN) :=
  ⟨splice_derivative_everywhere hqO hqN mq mv,
   splice_derivative_everywhere hvO hvN mv ma, splice_continuous haO haN ma⟩

/-- Any positive waiting time can still end in an acceleration jump.
One switch after the wait violates every proposed finite jerk bound. -/
theorem dwell_alone_not_jerk_limited {D J : ℝ} (hJ : 0 ≤ J) :
    ¬JerkLimited J (splice D (fun _ => 0) (fun _ => 1)) := by
  intro h
  have hp : 0 < J+1 := by linarith
  have he : 0 < 1/(J+1) := one_div_pos.mpr hp
  have ht : ¬D+1/(J+1) ≤ D := by linarith
  have hb := h D (D+1/(J+1)) (by linarith)
  simp only [splice, le_refl, ite_true, ht, ite_false, sub_zero, abs_one] at hb
  have hratio : J*(1/(J+1)) < 1 := by
    rw [mul_one_div, div_lt_one hp]; linarith
  have heq : D+1/(J+1)-D = 1/(J+1) := by ring
  rw [heq] at hb
  linarith

/-- With fixed initial state and duration, this is the exact scalar endpoint range
for one constant-jerk segment. It is not a full-state reachability theorem. -/
theorem reachable_endpoint_iff {z : State} {j h J : ℝ} (hh : 0 < h) :
    |j| ≤ J ↔
    |position z j h - (z.q+z.v*h+z.a*h^2/2)| ≤ J*h^3/6 := by
  have hp : 0 < h^3/6 := by positivity
  have heq : position z j h-(z.q+z.v*h+z.a*h^2/2) = j*(h^3/6) := by
    dsimp [position]; ring
  rw [heq, abs_mul, abs_of_pos hp]
  rw [show J*h^3/6 = J*(h^3/6) by ring]
  exact (mul_le_mul_iff_left₀ hp).symm

/-- A concrete 20 ms command segment. Bounds are SI units for a scalar translation. -/
theorem example_first_admitted :
    Admission ⟨0,1/10,0⟩ 10 (1/50) (-1/100) (1/100) (1/5) 1 10 := by
  constructor <;> norm_num [position, velocity, acceleration]

/-- The next segment can reverse jerk after just 20 ms without resetting the state. -/
theorem example_second_admitted :
    Admission (advance ⟨0,1/10,0⟩ 10 (1/50)) (-10) (1/50)
      (-1/100) (1/100) (1/5) 1 10 := by
  constructor <;> norm_num [advance, position, velocity, acceleration]

/-- The same state, duration and limits reject a 2.5 mm target.
It needs jerk 375 m/s^3; the limit remains 10 m/s^3. -/
theorem example_new_target_rejected :
    position ⟨0,1/10,0⟩ 375 (1/50) = 1/400 ∧
    ¬Admission ⟨0,1/10,0⟩ 375 (1/50) (-1/100) (1/100) (1/5) 1 10 := by
  constructor
  · norm_num [position]
  · intro h
    have hj := h.jerk
    norm_num at hj

/-- Reserving a future switch also protects the already executed prefix. -/
theorem splice_keeps_committed {now c t : ℝ} {old new : ℝ → ℝ}
    (hc : now ≤ c) (ht : t ≤ now) : splice c old new t = old t :=
  splice_keeps_prefix (ht.trans hc)

end LeanControls.SmoothReplan
