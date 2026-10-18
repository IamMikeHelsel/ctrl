module
public import DigitalHold
@[expose] public section
noncomputable section
namespace LeanControls.DelayedHold
open Set Filter
open DigitalHold

def center : ℝ := 141/1600

def startupLimit : ℝ := 1/2000

def actualCommand (D c : ℝ) (read : Bool → ℝ → State) (b : Bool) (t : ℝ) : ℝ :=
  if (if b then t < D else t ≤ D) then -1 else clip (command c (read b t))

/-- Global clock starts at the initial reading, not at dispatch. The known
pending command -1 is active before D, on the left at D. Digital command is
active on the right at D. Physical error is outside clipping. -/
structure Execution (H D : ℝ) (f : ℝ → State)
    (r d stamp : Bool → ℝ → ℝ) (read : Bool → ℝ → State) : Prop where
  continuous : ContinuousOn f (Icc 0 H)
  causal : ∀ b t, t ∈ Icc 0 H → 0 ≤ stamp b t ∧ stamp b t ≤ t ∧ t-stamp b t ≤ 1/1000
  error : ∀ b t, t ∈ Icc 0 H →
    |read b t 0-f (stamp b t) 0| ≤ 1/1000 ∧
    |read b t 1-f (stamp b t) 1| ≤ 1/100 ∧
    |read b t 2-f (stamp b t) 2| ≤ 1/20
  rate : ∀ b t, t ∈ Icc 0 H → 8 ≤ r b t ∧ r b t ≤ 12
  target_error : ∀ b t, t ∈ Icc 0 H → |d b t| ≤ 1/100
  right_ode : ∀ t ∈ Ico 0 H, ∀ i, HasDerivWithinAt (fun s => f s i)
    (rhs (r true t) (actualCommand D center read true t) (d true t) (f t) i) (Ici t) t
  left_ode : ∀ t ∈ Ioc 0 H, ∀ i, HasDerivWithinAt (fun s => f s i)
    (rhs (r false t) (actualCommand D center read false t) (d false t) (f t) i) (Iic t) t

/-- An evaluable initial admission condition around the inherited example.
The reading is at actual timestamp zero, with the original sensor bounds. -/
def Admitted (f : ℝ → State) : Prop :=
  |f 0 0-7/50| ≤ 1/1000 ∧ |f 0 1-(-1/100)| ≤ 1/100 ∧
    |f 0 2-(-117/100)| ≤ 1/20

section Startup
variable {H D : ℝ} {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
  (ex : Execution H D f r d stamp read) (hD : 0 ≤ D) (hDH : D ≤ H)
  (hi : Admitted f)
include ex hD hDH hi

theorem initial_bounds : |f 0 1| ≤ 1/50 ∧ |f 0 2| ≤ 61/50 := by
  have hv := abs_le.mp hi.2.1
  have ha := abs_le.mp hi.2.2
  exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨by linarith,by linarith⟩⟩

/-- The acceleration bound is derived from the pending-command dynamics. -/
theorem startup_acceleration : ∀ t ∈ Icc 0 D, |f t 2| ≤ 61/50 := by
  have hc : ContinuousOn (fun t => f t 2) (Icc 0 D) :=
    (continuous_apply 2).comp_continuousOn (ex.continuous.mono (Icc_subset_Icc_right hDH))
  have hai := (initial_bounds ex hD hDH hi).2
  have infl (ε : ℝ) (hε : 0 < ε) : ∀ t ∈ Icc 0 D, |f t 2| ≤ 61/50+ε := by
    let y : Bool → ℝ → ℝ := fun b t => (if b then f t 2 else -f t 2)-(61/50+ε)
    let dy : Bool → ℝ → ℝ := fun b t =>
      if b then r false t*(-1+d false t-f t 2) else -(r false t*(-1+d false t-f t 2))
    have hyc : ∀ b, ContinuousOn (y b) (Icc 0 D) := by
      intro b; cases b <;> dsimp [y] <;> fun_prop
    have hyd : ∀ b t, t ∈ Ioo 0 D → HasDerivWithinAt (y b) (dy b t) (Iic t) t := by
      intro b t ht
      have hd := ex.left_ode t ⟨ht.1,ht.2.le.trans hDH⟩ 2
      have hdt : t ≤ D := ht.2.le
      simp only [rhs,actualCommand,Bool.false_eq_true,ite_false,hdt,ite_true,Matrix.cons_val_two] at hd
      cases b
      · exact hd.neg.sub_const _
      · exact hd.sub_const _
    have hyi : ∀ b, y b 0 < 0 := by
      intro b
      have hh := abs_le.mp hai
      cases b <;> dsimp [y] <;> linarith
    have hyin : ∀ t ∈ Ioo 0 D, (∀ u ∈ Icc 0 t, ∀ b, y b u ≤ 0) → ∀ b, y b t = 0 → dy b t < 0 := by
      intro t ht _ b he
      have hr := ex.rate false t ⟨ht.1.le,ht.2.le.trans hDH⟩
      have hd := abs_le.mp (ex.target_error false t ⟨ht.1.le,ht.2.le.trans hDH⟩)
      cases b
      · dsimp [y] at he
        have hg : 0 < -1+d false t-f t 2 := by linarith
        have hp := mul_pos (by linarith [hr.1] : 0 < r false t) hg
        dsimp [dy]; linarith
      · dsimp [y] at he
        have hg : -1+d false t-f t 2 < 0 := by linarith
        have hp := mul_neg_of_pos_of_neg (by linarith [hr.1] : 0 < r false t) hg
        exact hp
    have hb := finite_prefix_barrier hD hyc hyd hyi hyin
    intro t ht
    have hp := hb t ht true
    have hn := hb t ht false
    dsimp [y] at hp hn
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  intro t ht
  exact le_of_forall_pos_le_add (fun ε hε => infl ε hε t ht)

theorem startup_jerk_bound (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 D) :
    |r b t*(-1+d b t-f t 2)| ≤ 669/25 := by
  have ha := abs_le.mp (startup_acceleration ex hD hDH hi t ht)
  have hr := ex.rate b t ⟨ht.1,ht.2.trans hDH⟩
  have hd := abs_le.mp (ex.target_error b t ⟨ht.1,ht.2.trans hDH⟩)
  have hb : |-1+d b t-f t 2| ≤ 223/100 := abs_le.mpr ⟨by linarith,by linarith⟩
  rw [abs_mul,abs_of_nonneg (by linarith [hr.1] : 0 ≤ r b t)]
  nlinarith [abs_nonneg (-1+d b t-f t 2)]

theorem startup_velocity (hlim : D ≤ startupLimit) :
    ∀ t ∈ Icc 0 D, |f t 1| ≤ 1061/50000 := by
  have hc : ContinuousOn (fun t => f t 1) (Icc 0 D) :=
    (continuous_apply 1).comp_continuousOn (ex.continuous.mono (Icc_subset_Icc_right hDH))
  have hd : ∀ t ∈ Ico 0 D, HasDerivWithinAt (fun s => f s 1) (f t 2) (Ici t) t :=
    fun t ht => ex.right_ode t ⟨ht.1,ht.2.trans_le hDH⟩ 1
  intro t ht
  have hm := age_bound hc hd (fun t ht => startup_acceleration ex hD hDH hi t ⟨ht.1,ht.2.le⟩)
    (s := 0) (by norm_num) ht.1 ht.2
  have hh := abs_sub (f t 1-f 0 1) (-f 0 1)
  have hv := (initial_bounds ex hD hDH hi).1
  have htri : |f t 1| ≤ |f t 1-f 0 1|+|f 0 1| := by
    simpa only [sub_add_cancel] using abs_add_le (f t 1-f 0 1) (f 0 1)
  norm_num [startupLimit] at hlim
  linarith [ht.2]

theorem startup_measurement_envelope (hlim : D ≤ startupLimit) :
    ∀ t ∈ Icc 0 D,
      |f t 0-7/50| ≤ 1/1000+(1061/50000)*t ∧
      |f t 1-(-1/100)| ≤ 1/100+(61/50)*t ∧
      |f t 2-(-117/100)| ≤ 1/20+(669/25)*t := by
  have hc (i : Fin 3) : ContinuousOn (fun t => f t i) (Icc 0 D) :=
    (continuous_apply i).comp_continuousOn (ex.continuous.mono (Icc_subset_Icc_right hDH))
  have hd0 : ∀ t ∈ Ico 0 D, HasDerivWithinAt (fun s => f s 0) (f t 1) (Ici t) t :=
    fun t ht => ex.right_ode t ⟨ht.1,ht.2.trans_le hDH⟩ 0
  have hd1 : ∀ t ∈ Ico 0 D, HasDerivWithinAt (fun s => f s 1) (f t 2) (Ici t) t :=
    fun t ht => ex.right_ode t ⟨ht.1,ht.2.trans_le hDH⟩ 1
  have hd2 : ∀ t ∈ Ico 0 D, HasDerivWithinAt (fun s => f s 2)
      (r true t*(-1+d true t-f t 2)) (Ici t) t := by
    intro t ht
    have hh := ex.right_ode t ⟨ht.1,ht.2.trans_le hDH⟩ 2
    simpa [actualCommand,ht.2,rhs] using hh
  intro t ht
  have hm0 := age_bound (hc 0) hd0 (fun u hu => startup_velocity ex hD hDH hi hlim u ⟨hu.1,hu.2.le⟩)
    (s := 0) (by norm_num) ht.1 ht.2
  have hm1 := age_bound (hc 1) hd1 (fun u hu => startup_acceleration ex hD hDH hi u ⟨hu.1,hu.2.le⟩)
    (s := 0) (by norm_num) ht.1 ht.2
  have hm2 := age_bound (hc 2) hd2 (fun u hu => startup_jerk_bound ex hD hDH hi true u ⟨hu.1,hu.2.le⟩)
    (s := 0) (by norm_num) ht.1 ht.2
  have h0 := abs_le.mp hm0; have h1 := abs_le.mp hm1; have h2 := abs_le.mp hm2
  have e0 := abs_le.mp hi.1; have e1 := abs_le.mp hi.2.1; have e2 := abs_le.mp hi.2.2
  exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩⟩

theorem startup_cube (hlim : D ≤ startupLimit) :
    ∀ t ∈ Icc 0 D, ∀ i, |coordinates center (f t) i| ≤ radius := by
  intro t ht i
  have hh := startup_measurement_envelope ex hD hDH hi hlim t ht
  have h0 := abs_le.mp hh.1; have h1 := abs_le.mp hh.2.1; have h2 := abs_le.mp hh.2.2
  norm_num [startupLimit] at hlim
  fin_cases i <;> dsimp [coordinates,center] <;> apply abs_le.mpr <;>
    constructor <;> norm_num [radius] <;> linarith [ht.1,ht.2]

/-- Startup feedback slope is separately derived under the pending command.
It is not borrowed from the digital mismatch hypothesis. -/
theorem startup_feedback_slope (hlim : D ≤ startupLimit) (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 D) :
    |-8*f t 1-6*f t 2-r b t*(-1+d b t-f t 2)/2| ≤ 7 := by
  have hv := abs_le.mp (startup_velocity ex hD hDH hi hlim t ht)
  have ha := abs_le.mp (startup_acceleration ex hD hDH hi t ht)
  have hr := ex.rate b t ⟨ht.1,ht.2.trans hDH⟩
  have hd := abs_le.mp (ex.target_error b t ⟨ht.1,ht.2.trans hDH⟩)
  have p0 := mul_nonneg (show 0 ≤ 6-r b t/2 by linarith [hr.2]) (show 0 ≤ f t 2+61/50 by linarith)
  have n0 := mul_nonneg (show 0 ≤ 6-r b t/2 by linarith [hr.2]) (show 0 ≤ 61/50-f t 2 by linarith)
  have p1 := mul_nonneg (show 0 ≤ r b t by linarith [hr.1]) (show 0 ≤ d b t+1/100 by linarith)
  have n1 := mul_nonneg (show 0 ≤ r b t by linarith [hr.1]) (show 0 ≤ 1/100-d b t by linarith)
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
end Startup


def actualMismatch (D : ℝ) (f : ℝ → State) (d : Bool → ℝ → ℝ)
    (read : Bool → ℝ → State) (b : Bool) (t : ℝ) : ℝ :=
  actualCommand D center read b t+d b t-command center (f t)

def actualSlope (D : ℝ) (f : ℝ → State) (r d : Bool → ℝ → ℝ)
    (read : Bool → ℝ → State) (b : Bool) (t : ℝ) : ℝ :=
  slopeRHS (r b t) (actualMismatch D f d read b t) (coordinates center (f t))

theorem startup_actual_slope {H D : ℝ} {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ}
    {read : Bool → ℝ → State} (ex : Execution H D f r d stamp read)
    (hD : 0 ≤ D) (hDH : D ≤ H) (hi : Admitted f) (hlim : D ≤ startupLimit)
    (t : ℝ) (ht : t ∈ Ico 0 D) : |actualSlope D f r d read true t| ≤ 7 := by
  have hh := startup_feedback_slope ex hD hDH hi hlim true t ⟨ht.1,ht.2.le⟩
  have he : actualSlope D f r d read true t =
      -8*f t 1-6*f t 2-r true t*(-1+d true t-f t 2)/2 := by
    dsimp [actualSlope,actualMismatch,actualCommand]
    rw [if_pos ht.2]
    dsimp [slopeRHS,coordinates,command]
    ring
  rwa [he]

section Prefix
variable {H D T K : ℝ} {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ}
  {read : Bool → ℝ → State} (ex : Execution H D f r d stamp read)
  (hT : T ≤ H) (hK : 0 ≤ K) (hKmax : K ≤ 1/16)
  (hz : ∀ t ∈ Icc 0 T, ∀ i, |coordinates center (f t) i| ≤ K)

include ex hT hz
theorem prefix_read_bound (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |command center (read b t)| ≤ 24*K+93/1000 := by
  have htH : t ∈ Icc 0 H := ⟨ht.1,ht.2.trans hT⟩
  have hs := ex.causal b t htH
  have he := ex.error b t htH
  have hb := (cube_physical_bounds (hz (stamp b t) ⟨hs.1,hs.2.1.trans ht.2⟩)).2.2.2
  have hm := measurement_cost (c := center) he.1 he.2.1 he.2.2
  calc |command center (read b t)| ≤ |command center (read b t)-command center (f (stamp b t))|+
      |command center (f (stamp b t))| := by
        simpa only [sub_add_cancel] using abs_add_le (command center (read b t)-command center (f (stamp b t))) (command center (f (stamp b t)))
    _ ≤ 24*K+93/1000 := by linarith

include hKmax
theorem prefix_clip_eq (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    clip (command center (read b t)) = command center (read b t) := by
  apply clip_eq
  have hb := prefix_read_bound ex hT hz b t ht
  linarith

theorem coarse_mismatch (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |mismatch center f d read b t| ≤ 48*K+103/1000 := by
  have htH : t ∈ Icc 0 H := ⟨ht.1,ht.2.trans hT⟩
  have hr := prefix_read_bound ex hT hz b t ht
  have hk := (cube_physical_bounds (hz t ht)).2.2.2
  have hd := ex.target_error b t htH
  dsimp [mismatch]
  rw [prefix_clip_eq ex hT hKmax hz b t ht]
  calc |command center (read b t)+d b t-command center (f t)| ≤
      |command center (read b t)|+|d b t|+|command center (f t)| := by
        have h1 := abs_sub (command center (read b t)+d b t) (command center (f t))
        have h2 := abs_add_le (command center (read b t)) (d b t)
        linarith
    _ ≤ 48*K+103/1000 := by linarith

theorem improve_mismatch {L : ℝ} (hL : 0 ≤ L)
    (hslope : ∀ t ∈ Ico 0 T,
      |actualSlope D f r d read true t| ≤ L)
    (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |mismatch center f d read b t| ≤ 103/1000+L/1000 := by
  have htH : t ∈ Icc 0 H := ⟨ht.1,ht.2.trans hT⟩
  have hs := ex.causal b t htH
  have he := ex.error b t htH
  have hm := measurement_cost (c := center) he.1 he.2.1 he.2.2
  have hc : ContinuousOn (fun t => command center (f t)) (Icc 0 T) := by
    have hh : ∀ i, ContinuousOn (fun t => f t i) (Icc 0 T) := fun i =>
      (continuous_apply i).comp_continuousOn (ex.continuous.mono (Icc_subset_Icc_right hT))
    dsimp [command]; fun_prop
  have hd : ∀ x ∈ Ico 0 T, HasDerivWithinAt (fun t => command center (f t))
      (actualSlope D f r d read true x) (Ici x) x := by
    intro x hx
    exact command_deriv (ex.right_ode x ⟨hx.1,hx.2.trans_le hT⟩)
  have hmove := age_bound hc hd hslope hs.1 hs.2.1 ht.2
  have hage := mul_le_mul_of_nonneg_left hs.2.2 hL
  have hnoise := ex.target_error b t htH
  have htri : |command center (read b t)+d b t-command center (f t)| ≤
      |command center (read b t)-command center (f (stamp b t))|+
      |command center (f t)-command center (f (stamp b t))|+|d b t| := by
    calc _ = |(command center (read b t)-command center (f (stamp b t))) -
        (command center (f t)-command center (f (stamp b t))) + d b t| := by congr 1; ring
      _ ≤ |(command center (read b t)-command center (f (stamp b t))) -
        (command center (f t)-command center (f (stamp b t)))|+|d b t| := abs_add_le _ _
      _ ≤ _ := by
        have hh := abs_sub (command center (read b t)-command center (f (stamp b t))) (command center (f t)-command center (f (stamp b t)))
        linarith
  dsimp [mismatch]
  rw [prefix_clip_eq ex hT hKmax hz b t ht]
  linarith


include hK
/-- The second pass covers the complete sample history, including pending
command time. Neither mismatch nor ongoing cube invariance is a premise. -/
theorem prefix_budget (hKR : radius ≤ K) (hD : 0 ≤ D) (hDH : D ≤ H)
    (hi : Admitted f) (hlim : D ≤ startupLimit) (b : Bool) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |mismatch center f d read b t| ≤ 2*K := by
  have hsl0 : ∀ x ∈ Ico 0 T, |actualSlope D f r d read true x| ≤ 384*K+618/1000 := by
    intro x hx
    by_cases hb : x < D
    · have hh := startup_actual_slope ex hD hDH hi hlim x ⟨hx.1,hb⟩
      norm_num [radius] at hKR
      linarith
    · have hxc : x ∈ Icc 0 T := ⟨hx.1,hx.2.le⟩
      have hh := slope_bound (w := mismatch center f d read true x) hK
        (ex.rate true x ⟨hx.1,hx.2.le.trans hT⟩) (hz x hxc)
      have hw := coarse_mismatch ex hT hKmax hz true x hxc
      have he : actualSlope D f r d read true x =
          slopeRHS (r true x) (mismatch center f d read true x) (coordinates center (f x)) := by
        simp [actualSlope,actualMismatch,actualCommand,mismatch,hb]
      rw [he]
      linarith
  have hw0 := improve_mismatch ex hT hKmax hz (by positivity : 0 ≤ 384*K+618/1000) hsl0
  have hsl1 : ∀ x ∈ Ico 0 T, |actualSlope D f r d read true x| ≤ 7 := by
    intro x hx
    by_cases hb : x < D
    · exact startup_actual_slope ex hD hDH hi hlim x ⟨hx.1,hb⟩
    · have hxc : x ∈ Icc 0 T := ⟨hx.1,hx.2.le⟩
      have hh := slope_bound (w := mismatch center f d read true x) hK
        (ex.rate true x ⟨hx.1,hx.2.le.trans hT⟩) (hz x hxc)
      have hw := hw0 true x hxc
      have he : actualSlope D f r d read true x =
          slopeRHS (r true x) (mismatch center f d read true x) (coordinates center (f x)) := by
        simp [actualSlope,actualMismatch,actualCommand,mismatch,hb]
      rw [he]
      linarith
  have hw1 := improve_mismatch ex hT hKmax hz (by norm_num : (0:ℝ) ≤ 7) hsl1 b t ht
  norm_num [radius] at hKR
  linarith
end Prefix

/-- All-time safety from a measured admission, including the real delay. -/
theorem delayed_invariant {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hDH : D ≤ H) (hlim : D ≤ startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (ex : Execution H D f r d stamp read) (hreading : Admitted f) :
    ∀ t ∈ Icc 0 H, ∀ i, |coordinates center (f t) i| ≤ radius := by
  have hi := startup_cube ex hD hDH hreading hlim 0 ⟨le_rfl,hD⟩
  let z := fun t => coordinates center (f t)
  have hradius : 0 ≤ radius := by norm_num [radius]
  have hzc (i : Fin 3) : ContinuousOn (fun t => z t i) (Icc 0 H) := by
    have hfc (j : Fin 3) := (continuous_apply j).comp_continuousOn ex.continuous
    fin_cases i <;> dsimp [z,coordinates] <;> fun_prop
  have inflated (ε : ℝ) (hε : 0 < ε) (hsmall : ε*(1+H) ≤ 1/16-radius) :
      ∀ t ∈ Icc 0 H, ∀ i, |z t i| ≤ radius+ε*(1+t) := by
    let K := fun t : ℝ => radius+ε*(1+t)
    let y : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then z t p.1 else -z t p.1)-K t
    let dy : (Fin 3 × Bool) → ℝ → ℝ := fun p t =>
      (if p.2 then transformedRHS (r false t) (actualMismatch D f d read false t) (z t) p.1
       else -transformedRHS (r false t) (actualMismatch D f d read false t) (z t) p.1)-ε
    have hKc : Continuous K := by dsimp [K]; fun_prop
    have hKd (t : ℝ) : HasDerivAt K ε t := by
      convert (((hasDerivAt_id t).const_add 1).const_mul ε).const_add radius using 1 <;> simp [K]
    have hyc (p : Fin 3 × Bool) : ContinuousOn (y p) (Icc 0 H) := by
      obtain ⟨i,b⟩ := p
      cases b <;> dsimp [y] <;> fun_prop
    have hyd (p : Fin 3 × Bool) (t : ℝ) (ht : t ∈ Ioo 0 H) :
        HasDerivWithinAt (y p) (dy p t) (Iic t) t := by
      have hd := coordinate_deriv (c := center) (ex.left_ode t ⟨ht.1,ht.2.le⟩) p.1
      obtain ⟨i,b⟩ := p
      cases b
      · exact hd.neg.sub (hKd t).hasDerivWithinAt
      · exact hd.sub (hKd t).hasDerivWithinAt
    have hyi (p : Fin 3 × Bool) : y p 0 < 0 := by
      obtain ⟨i,b⟩ := p
      have hii := abs_le.mp (hi i)
      cases b <;> dsimp [y,K,z] <;> linarith
    have hyin (t : ℝ) (ht : t ∈ Ioo 0 H)
        (hall : ∀ u ∈ Icc 0 t, ∀ p, y p u ≤ 0)
        (p : Fin 3 × Bool) (he : y p t = 0) : dy p t < 0 := by
      have htc : t ∈ Icc 0 H := ⟨ht.1.le,ht.2.le⟩
      have hKR : radius ≤ K t := by dsimp [K]; nlinarith [ht.1]
      have hKpos : 0 ≤ K t := hradius.trans hKR
      have hKmax : K t ≤ 1/16 := by dsimp [K]; nlinarith [ht.2]
      have hzt (u : ℝ) (hu : u ∈ Icc 0 t) (i : Fin 3) : |z u i| ≤ K t := by
        have hp := hall u hu (i,true)
        have hn := hall u hu (i,false)
        dsimp [y,K] at hp hn ⊢
        exact abs_le.mpr ⟨by nlinarith [hu.2],by nlinarith [hu.2]⟩
      by_cases hpre : t ≤ D
      · have hs := abs_le.mp (startup_cube ex hD hDH hreading hlim t ⟨ht.1.le,hpre⟩ p.1)
        obtain ⟨i,b⟩ := p
        cases b <;> dsimp [y,K,z] at he <;> dsimp at hs <;> exfalso <;> nlinarith [ht.1]
      have hw := prefix_budget ex ht.2.le hKpos hKmax hzt hKR hD hDH hreading hlim false t ⟨ht.1.le,le_rfl⟩
      have heff : actualMismatch D f d read false t = mismatch center f d read false t := by
        simp [actualMismatch,actualCommand,mismatch,hpre]
      obtain ⟨i,b⟩ := p
      have hface := cube_face hKpos le_rfl (ex.rate false t htc).1 (ex.rate false t htc).2 hw
        (hzt t ⟨ht.1.le,le_rfl⟩) i
      cases b
      · dsimp [y] at he
        have hzi : z t i = -K t := by linarith
        have hh := hface.2 hzi
        dsimp [dy]
        rw [heff]
        linarith
      · dsimp [y] at he
        have hzi : z t i = K t := by linarith
        have hh := hface.1 hzi
        dsimp [dy]
        rw [heff]
        linarith
    have hbar := finite_prefix_barrier hH hyc hyd hyi hyin
    intro t ht i
    have hp := hbar t ht (i,true)
    have hn := hbar t ht (i,false)
    dsimp [y,K] at hp hn
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  intro t ht i
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < 1+H := by linarith
  let δ := min (ε/(1+H)) ((1/16-radius)/(1+H))
  have hδ : 0 < δ := lt_min (div_pos hε hden) (div_pos (by norm_num [radius]) hden)
  have hδ1 : δ*(1+H) ≤ ε := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left (ε/(1+H)) ((1/16-radius)/(1+H))) hden.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hden)] using hh
  have hδ2 : δ*(1+H) ≤ 1/16-radius := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (ε/(1+H)) ((1/16-radius)/(1+H))) hden.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hden)] using hh
  have hh := inflated δ hδ hδ2 t ht i
  change |z t i| ≤ radius+ε
  nlinarith [ht.2]


/-- The first reading is at global zero, dispatched at D. It remains held
until the next dispatch. Earlier startup time is not erased from its age. -/
structure IsSchedule (H D : ℝ) (q : Schedule) (stamp : Bool → ℝ → ℝ)
    (read : Bool → ℝ → State) : Prop where
  first_dispatch : q.dispatch 0 = D
  first_sample : q.sample 0 = 0
  startup_index : ∀ b t, t ∈ Icc 0 D → q.index b t = 0
  sample_order : ∀ n, 0 ≤ q.sample n ∧ q.sample n ≤ q.dispatch n
  dispatch_order : StrictMono q.dispatch
  locally_finite : ∀ T : ℝ, Set.Finite {n | q.dispatch n ≤ T}
  right_cell : ∀ t ∈ Ico D H,
    q.dispatch (q.index true t) ≤ t ∧ t < q.dispatch (q.index true t+1)
  left_cell : ∀ t ∈ Ioc D H,
    q.dispatch (q.index false t) < t ∧ t ≤ q.dispatch (q.index false t+1)
  timestamp : ∀ b t, t ∈ Icc 0 H → stamp b t = q.sample (q.index b t)
  held_reading : ∀ b t, t ∈ Icc 0 H → read b t = q.measurement (q.index b t)

def exampleReading : State := ![7/50,-1/100,-117/100]

theorem observation_admission {H D : ℝ} (hD : 0 ≤ D) (hDH : D ≤ H)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State} {q : Schedule}
    (ex : Execution H D f r d stamp read) (hs : IsSchedule H D q stamp read)
    (hm : q.measurement 0 = exampleReading) : Admitted f := by
  have ht : (0:ℝ) ∈ Icc 0 H := ⟨le_rfl,hD.trans hDH⟩
  have hts := hs.timestamp true 0 ht
  have hread := hs.held_reading true 0 ht
  rw [hs.startup_index true 0 ⟨le_rfl,hD⟩,hs.first_sample] at hts
  rw [hs.startup_index true 0 ⟨le_rfl,hD⟩,hm] at hread
  have he := ex.error true 0 ht
  rw [hts,hread] at he
  dsimp [exampleReading] at he
  dsimp [Admitted]
  simpa only [abs_sub_comm] using he

theorem first_dispatch_reading {H D : ℝ} (hD : 0 ≤ D) (hDH : D ≤ H)
    {stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State} {q : Schedule}
    (hs : IsSchedule H D q stamp read) (b : Bool) :
    stamp b D = 0 ∧ read b D = q.measurement 0 := by
  have ht : D ∈ Icc 0 H := ⟨hD,hDH⟩
  exact ⟨by rw [hs.timestamp b D ht,hs.startup_index b D ⟨hD,le_rfl⟩,hs.first_sample],
    by rw [hs.held_reading b D ht,hs.startup_index b D ⟨hD,le_rfl⟩]⟩

theorem right_held_reading {H D t : ℝ} {q : Schedule}
    {stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (hD : 0 ≤ D) (hs : IsSchedule H D q stamp read) (ht : t ∈ Ico D H) (n : ℕ)
    (hn : q.dispatch n ≤ t ∧ t < q.dispatch (n+1)) :
    stamp true t = q.sample n ∧ read true t = q.measurement n := by
  have hi := hs.right_cell t ht
  have heq : q.index true t = n := by
    rcases lt_trichotomy (q.index true t) n with hlt | heq | hgt
    · have hh := hs.dispatch_order.monotone (show q.index true t+1 ≤ n by omega)
      linarith [hi.2,hn.1]
    · exact heq
    · have hh := hs.dispatch_order.monotone (show n+1 ≤ q.index true t by omega)
      linarith [hi.1,hn.2]
  have htc : t ∈ Icc 0 H := ⟨hD.trans ht.1,ht.2.le⟩
  exact ⟨by rw [hs.timestamp true t htc,heq],by rw [hs.held_reading true t htc,heq]⟩

/-- A first reading does not receive a new millisecond when it is dispatched. -/
theorem first_cell_age {H D t : ℝ} {q : Schedule}
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (hD : 0 ≤ D) (ex : Execution H D f r d stamp read)
    (hs : IsSchedule H D q stamp read) (ht : t ∈ Ico D H)
    (hn : t < q.dispatch 1) : t ≤ 1/1000 := by
  have hread := right_held_reading hD hs ht 0 ⟨by simpa [hs.first_dispatch] using ht.1,hn⟩
  have hc := ex.causal true t ⟨hD.trans ht.1,ht.2.le⟩
  rw [hread.1,hs.first_sample] at hc
  simpa only [sub_zero] using hc.2.2

theorem no_first_hold_after_full_age {H D t : ℝ} {q : Schedule}
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State}
    (hD : (1:ℝ)/1000 ≤ D) (ex : Execution H D f r d stamp read)
    (hs : IsSchedule H D q stamp read) (ht : t ∈ Ioo D H)
    (hn : t < q.dispatch 1) : False := by
  have hh := first_cell_age (by linarith : 0 ≤ D) ex hs ⟨ht.1.le,ht.2⟩ hn
  linarith [ht.1]

/-- This rejects extending the startup slope-7 guard to a pending -2 command.
It does not assert that this stronger braking command causes a safety violation. -/
theorem stronger_pending_rejects_slope_guard :
    |-8*(-1/100:ℝ)-6*(-117/100)-12*(-2-(-117/100))/2| = 302/25 ∧
    (7:ℝ) < 302/25 := by norm_num

/-- The measured example, positive or zero bounded delay, known pending
command, and the global sampled contract imply safety through the delay and
through every later dispatch. No endpoint cube is a premise. -/
theorem delayed_sampled_hold {H D : ℝ} (hD : 0 ≤ D) (hDH : D ≤ H) (hlim : D ≤ startupLimit)
    {f : ℝ → State} {r d stamp : Bool → ℝ → ℝ} {read : Bool → ℝ → State} {q : Schedule}
    (ex : Execution H D f r d stamp read) (hs : IsSchedule H D q stamp read)
    (hm : q.measurement 0 = exampleReading) :
    (∀ b, stamp b D = 0 ∧ read b D = exampleReading) ∧
    (∀ t ∈ Icc 0 H, ∀ i, |coordinates center (f t) i| ≤ radius) ∧
    (∀ t ∈ Icc 0 H, 163/5000 ≤ f t 0 ∧ f t 0 ≤ 2873/20000 ∧
      |f t 1| ≤ 8*radius ∧ |f t 2| ≤ 64*radius ∧
      ∀ b, |actualCommand D center read b t+d b t| ≤ 3589/2500) := by
  have hH := hD.trans hDH
  have hi := observation_admission hD hDH ex hs hm
  have hz := delayed_invariant hH hD hDH hlim ex hi
  refine ⟨?_,hz,?_⟩
  · intro b
    simpa only [hm] using first_dispatch_reading hD hDH hs b
  · intro t ht
    have hp := cube_physical_bounds (hz t ht)
    have htube := abs_le.mp hp.1
    norm_num [center,radius] at htube
    refine ⟨by linarith,by linarith,hp.2.1,hp.2.2.1,?_⟩
    intro b
    have hr := prefix_read_bound ex le_rfl hz b t ht
    have hc := prefix_clip_eq ex le_rfl (by norm_num [radius] : radius ≤ 1/16) hz b t ht
    have hd := ex.target_error b t ht
    by_cases hb : (if b then t < D else t ≤ D)
    · rw [actualCommand,if_pos hb]
      have hh := abs_add_le (-1:ℝ) (d b t)
      norm_num at hh
      linarith
    · rw [actualCommand,if_neg hb,hc]
      have hh := abs_add_le (command center (read b t)) (d b t)
      norm_num [radius] at hr
      linarith

end LeanControls.DelayedHold
