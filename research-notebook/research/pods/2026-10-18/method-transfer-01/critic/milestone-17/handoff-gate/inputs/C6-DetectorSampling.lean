module
public import DetectorBridge
public import Mathlib.Algebra.Order.Floor.Semiring
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.DetectorSampling
open Set Filter
open UncertainLag (State)
open VariableResponse DetectorBridge

def SensorBox (z m : State) : Prop :=
  |m 0-z 0| ≤ 1/1000 ∧ |m 1-z 1| ≤ 1/100 ∧ |m 2-z 2| ≤ 1/20

def sample (n : ℕ) : ℝ := (n:ℝ)/2000

def Readings (f : ℝ → State) (m : ℕ → State) : Prop :=
  ∀ n, n ≤ 1060 → SensorBox (f (sample n)) (m n)

variable {f : ℝ → State} {rLoss qLoss rBrake qBrake : ℝ → ℝ}
variable (ex : BrakingExecution f rLoss qLoss rBrake qBrake)
include ex

theorem brake_velocity_deriv {t : ℝ} (ht : t ∈ Ioo (1/20) (53/100)) :
    HasDerivAt (fun s => f s 1) (f t 2) t := by
  have hd := ex.brake.ode (t-1/20) ⟨by linarith [ht.1],by linarith [ht.2]⟩ 1
  have hh := hd.comp t ((hasDerivAt_id t).sub_const (1/20:ℝ))
  convert hh using 1 <;> simp [Function.comp_def]

theorem post_zero_velocity {τ σ : ℝ} (hτ : τ ∈ Icc (39/122:ℝ) (529/1000))
    (hz : f τ 1=0) (hσ : τ ≤ σ ∧ σ ≤ τ+1/1000) (hend : σ ≤ 53/100) :
    -61/50000 ≤ f σ 1 ∧ f σ 1 ≤ 0 := by
  have hc : ContinuousOn (fun s => f (τ+s) 1) (Icc 0 (σ-τ)) :=
    ((continuous_apply 1).comp_continuousOn ex.continuous).comp
      (continuous_const.add continuous_id).continuousOn (by
        intro s hs; exact ⟨by linarith [hs.1,hτ.1],by linarith [hs.2]⟩)
  have hd (s : ℝ) (hs : s ∈ Ioo 0 (σ-τ)) :
      HasDerivAt (fun u => f (τ+u) 1) (f (τ+s) 2) s := by
    have hh := (brake_velocity_deriv ex (t := τ+s)
      ⟨by linarith [hτ.1,hs.1],by linarith [hs.2]⟩).comp s ((hasDerivAt_id s).const_add τ)
    simpa only [Function.comp_def,id_eq,mul_one] using hh
  have hlo := derivative_comparison (show 0 ≤ σ-τ by linarith [hσ.1])
    (f := fun s : ℝ => -(61/50)*s) (g := fun s => f (τ+s) 1)
    (by fun_prop) hc (fun s _ => by simpa using (hasDerivAt_id s).const_mul (-(61/50:ℝ))) hd
    (by simpa [hz]) (by
      intro s hs; simpa only [neg_div] using all_acceleration_lower ex (τ+s)
        ⟨by linarith [hτ.1,hs.1],by linarith [hs.2]⟩)
  have hhi := derivative_comparison (show 0 ≤ σ-τ by linarith [hσ.1])
    hc (g := fun _ : ℝ => 0) continuousOn_const hd (fun s _ => hasDerivAt_const s 0)
    (by simpa [hz]) (by
      intro s hs; have hh := late_acceleration_upper ex (τ+s)
        ⟨by linarith [hτ.1,hs.1],by linarith [hs.2]⟩; linarith)
  have hl := hlo (σ-τ) ⟨by linarith [hσ.1],le_rfl⟩
  have hu := hhi (σ-τ) ⟨by linarith [hσ.1],le_rfl⟩
  simp only [add_sub_cancel] at hl hu
  constructor <;> linarith [hσ.2]

theorem guard_after_zero {τ σ : ℝ} {m : State}
    (hτ : τ ∈ Icc (39/122:ℝ) (529/1000)) (hz : f τ 1=0)
    (hσ : τ ≤ σ ∧ σ ≤ τ+1/1000) (hend : σ ≤ 53/100)
    (hm : SensorBox (f σ) m) : ClearancePolicy.Guard m ∧ m 2 ≤ -31/140 := by
  have htime : σ ∈ Icc (0:ℝ) (53/100) := ⟨by linarith [hτ.1,hσ.1],hend⟩
  have hx := all_position_upper ex σ htime
  have hv := post_zero_velocity ex hτ hz hσ hend
  have ha := all_acceleration_lower ex σ htime
  have hau := late_acceleration_upper ex σ ⟨by linarith [hτ.1,hσ.1],hend⟩
  obtain ⟨hmx,hmv,hma⟩ := hm
  have exx := abs_le.mp hmx; have exv := abs_le.mp hmv; have exa := abs_le.mp hma
  refine ⟨⟨by linarith,abs_le.mpr ⟨by linarith,by linarith⟩,by linarith,by linarith⟩,by linarith⟩

/-- The finite grid has coverage. The selected reading is valid for every
error realization in the original sensor box. -/
theorem finite_guard_hit {m : ℕ → State} (hm : Readings f m) :
    ∃ τ ∈ Icc (39/122:ℝ) (529/1000), f τ 1=0 ∧
      ∃ N : ℕ, N ≤ 1058 ∧ τ ≤ sample N ∧ sample N ≤ τ+1/2000 ∧
        ClearancePolicy.Guard (m N) := by
  obtain ⟨τ,hτ,hz,hbefore⟩ := first_zero ex
  let N : ℕ := ⌈2000*τ⌉₊
  have hN : N ≤ 1058 := Nat.ceil_le.mpr (by norm_num; linarith [hτ.2])
  have hnlo := Nat.le_ceil (2000*τ)
  have hnhi := Nat.ceil_lt_add_one (show 0 ≤ 2000*τ by linarith [hτ.1])
  have hlo : τ ≤ sample N := by dsimp [sample,N]; linarith
  have hhi : sample N ≤ τ+1/2000 := by dsimp [sample,N]; linarith
  have hg := guard_after_zero ex hτ hz ⟨hlo,by linarith⟩
    (by linarith [hτ.2]) (hm N (by omega))
  exact ⟨τ,hτ,hz,N,hN,hlo,hhi,hg.1⟩

/-- A first qualifying index exists in the finite list. It may precede the
physical first zero. This says nothing about an actual switch or its prefix. -/
theorem finite_first_guard {m : ℕ → State} (hm : Readings f m) :
    ∃ k : ℕ, k ≤ 1058 ∧ ClearancePolicy.Guard (m k) ∧
      (∀ j < k, ¬ ClearancePolicy.Guard (m j)) ∧
      ∀ D ∈ Icc (0:ℝ) (1/2000), sample k+D ≤ 53/100 := by
  classical
  obtain ⟨τ,hτ,hz,N,hN,hlo,hhi,hg⟩ := finite_guard_hit ex hm
  have he : ∃ k, ClearancePolicy.Guard (m k) := ⟨N,hg⟩
  let k := Nat.find he
  have hk : k ≤ N := Nat.find_min' he hg
  refine ⟨k,hk.trans hN,Nat.find_spec he,?_,?_⟩
  · exact fun j hj => Nat.find_min he hj
  · intro D hD
    have hcast : (k:ℝ) ≤ (1058:ℝ) := by exact_mod_cast hk.trans hN
    dsimp [sample]; linarith [hD.2]

omit ex in
theorem common_latency_clocks (σ D : ℝ) (hD : D ∈ Icc (0:ℝ) (1/2000)) :
    StrictMono (fun n : ℕ => σ+D+sample n) ∧
    (∀ n : ℕ, (σ+sample n)-σ=sample n ∧ (σ+D+sample n)-σ=D+sample n) ∧
    (∀ n : ℕ, (σ+D+sample (n+1))-(σ+sample n)=D+1/2000) ∧
    D+1/2000 ≤ 1/1000 ∧
    (∀ n : ℕ, (σ+D+sample n)-(σ+sample n)=D) := by
  refine ⟨?_,?_,?_,by linarith [hD.2],?_⟩
  · intro i j hij
    have hcast : (i:ℝ)<(j:ℝ) := by exact_mod_cast hij
    dsimp [sample]; linarith
  · intro n; constructor <;> ring
  · intro n; simp [sample,Nat.cast_add]; ring
  · intro n; ring

/- Age holds throughout a held cell, including the incoming dispatch endpoint.
At that endpoint the outgoing command uses the younger next reading. -/
omit ex in
theorem held_cell_age {σ D t : ℝ} (hD : D ∈ Icc (0:ℝ) (1/2000)) (n : ℕ)
    (ht : t ∈ Icc (σ+D+sample n) (σ+D+sample (n+1))) :
    σ+sample n ≤ t ∧ t-(σ+sample n) ≤ 1/1000 := by
  have he := (common_latency_clocks σ D hD).2.2.1 n
  constructor <;> linarith [ht.1,ht.2,hD.1,hD.2]

omit ex in
theorem old_queued_stamp_stays_negative {p σ : ℝ} (h : p<σ) : p-σ<0 := by linarith

omit ex in
theorem one_millisecond_period_fails : (1/1000:ℝ)+(1/2000)>1/1000 := by norm_num

omit ex in
theorem variable_latency_tie : (0:ℝ)+1/2000 = 1/2000+0 := by norm_num

/-- A strictly increasing sequence with bounded gaps can stay before the
entire detector window. This is a physical-time coverage counterexample. -/
def zeno (n : ℕ) : ℝ := (1/2000)*(1-1/((n:ℝ)+1))

omit ex in
theorem zeno_bounded (n : ℕ) : 0 ≤ zeno n ∧ zeno n < 1/2000 := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hp : 0 < (n:ℝ)+1 := by positivity
  have hi : 0 < 1/((n:ℝ)+1) := by positivity
  have hh : 1/((n:ℝ)+1) ≤ 1 := (div_le_one hp).mpr (by linarith)
  dsimp [zeno]; constructor <;> linarith

omit ex in
theorem zeno_gap (n : ℕ) : 0 < zeno (n+1)-zeno n ∧ zeno (n+1)-zeno n ≤ 1/4000 := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have h1 : 0 < (n:ℝ)+1 := by positivity
  have h2 : 0 < (n:ℝ)+2 := by positivity
  have he : zeno (n+1)-zeno n = 1/(2000*((n:ℝ)+1)*((n:ℝ)+2)) := by
    simp [zeno,Nat.cast_add]; field_simp; ring
  rw [he]
  refine ⟨by positivity,?_⟩
  apply (div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ)<4000)).mpr
  nlinarith [sq_nonneg (n:ℝ)]

end LeanControls.DetectorSampling
