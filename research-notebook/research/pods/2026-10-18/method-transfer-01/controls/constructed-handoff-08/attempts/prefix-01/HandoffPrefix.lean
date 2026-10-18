module
public import ConstructiveWitness
public import ReviewControls
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.ConstructedHandoff
open Set Filter DigitalHold ConstructiveHold DetectorBridge DetectorSampling

def First (m : ℕ → State) (k : ℕ) : Prop :=
  ClearancePolicy.Guard (m k) ∧ ∀ j < k, ¬ ClearancePolicy.Guard (m j)

theorem first_unique {m : ℕ → State} {j k : ℕ} (hj : First m j) (hk : First m k) : j=k := by
  rcases lt_trichotomy j k with h | h | h
  · exact False.elim (hk.2 j h hj.1)
  · exact h
  · exact False.elim (hj.2 k h hk.1)

theorem first_prefix_stable {m m' : ℕ → State} {k : ℕ} (hk : First m k)
    (he : ∀ j ≤ k, m' j=m j) : First m' k := by
  exact ⟨by rw [he k le_rfl]; exact hk.1,fun j hj => by rw [he j hj.le]; exact hk.2 j hj⟩

variable {f : ℝ → State} {rL qL rB qB : ℝ → ℝ} {m : ℕ → State} {k : ℕ}

theorem decision_bounds (ex : BrakingExecution f rL qL rB qB) (hm : Readings f m)
    (hk : k≤1058) (hg : ClearancePolicy.Guard (m k)) :
    605≤k ∧ (1/20:ℝ)<grid k ∧ grid k+h<53/100 := by
  have hc : (k:ℝ)≤1058 := by exact_mod_cast hk
  have ht : sample k ∈ Icc (0:ℝ) (53/100) := ⟨by unfold sample; positivity,by dsimp [sample]; linarith⟩
  have hl := DetectorReview.guard_time_lower ex ht (hm k (by omega)) hg
  have hn : (605:ℝ)≤k := by
    by_contra hh
    have hk' : k<605 := by exact_mod_cast (lt_of_not_ge hh)
    have hx : (k:ℝ)≤604 := by exact_mod_cast (show k≤604 by omega)
    dsimp [sample] at hl; linarith
  refine ⟨by exact_mod_cast hn,?_,?_⟩ <;> dsimp [grid] <;> linarith

def pending (f : ℝ → State) (σ s : ℝ) : State := f (σ+s)
def prefixRate (r : ℝ → ℝ) (σ : ℝ) (_ : Bool) (s : ℝ) : ℝ := r (σ+s-1/20)
def prefixError (q : ℝ → ℝ) (σ : ℝ) (_ : Bool) (s : ℝ) : ℝ := q (σ+s-1/20)+121/100

theorem recovered_deriv (ex : BrakingExecution f rL qL rB qB) {t : ℝ}
    (ht : t ∈ Ioo (1/20:ℝ) (53/100)) (i : Fin 3) :
    HasDerivAt (fun s => f s i)
      (![f t 1,f t 2,rB (t-1/20)*(qB (t-1/20)-f t 2)] i) t := by
  have hd := ex.brake.ode (t-1/20) ⟨by linarith [ht.1],by linarith [ht.2]⟩ i
  have hh := hd.comp t ((hasDerivAt_id t).sub_const (1/20:ℝ))
  convert hh using 1 <;> simp [Function.comp_def]

theorem pending_deriv (ex : BrakingExecution f rL qL rB qB) {σ s : ℝ}
    (hσ : (1/20:ℝ)<σ) (hend : σ+h<53/100) (hs : s ∈ Icc 0 h) (i : Fin 3) :
    HasDerivAt (fun u => pending f σ u i)
      (rhs (prefixRate rB σ true s) (-121/100) (prefixError qB σ true s) (pending f σ s) i) s := by
  have hd := (recovered_deriv ex (t:=σ+s) ⟨by linarith [hs.1],by linarith [hs.2]⟩ i).comp s
    ((hasDerivAt_id s).const_add σ)
  simpa [pending,prefixRate,prefixError,rhs,Function.comp_def] using hd

theorem pending_execution (ex : BrakingExecution f rL qL rB qB) (hm : Readings f m)
    (hk : k≤1058) (hg : ClearancePolicy.Guard (m k)) :
    ClearanceAdmission.Execution h h (m k) (pending f (grid k))
      (prefixRate rB (grid k)) (prefixError qB (grid k)) (fun _ _ => 0) (fun _ _ => m k) := by
  have hb := decision_bounds ex hm hk hg
  constructor
  · exact ex.continuous.comp (continuous_const.add continuous_id).continuousOn (by
      intro s hs; exact ⟨by linarith [hb.2.1,hs.1],by linarith [hb.2.2,hs.2]⟩)
  · intro b s hs; exact ⟨le_rfl,hs.1,by have hh : s≤(1/2000:ℝ) := hs.2; linarith⟩
  · intro b s hs; simpa [pending,grid,sample] using hm k (by omega)
  · intro b s hs; exact ex.brake_rate _ ⟨by linarith [hb.2.1,hs.1],by linarith [hb.2.2,hs.2]⟩
  · intro b s hs
    have hh := ex.brake_target (grid k+s-1/20) ⟨by linarith [hb.2.1,hs.1],by linarith [hb.2.2,hs.2]⟩
    dsimp [prefixError]; exact abs_le.mpr ⟨by linarith [hh.1],by linarith [hh.2]⟩
  · intro s hs i
    have hd := (pending_deriv ex hb.2.1 hb.2.2 ⟨hs.1,hs.2.le⟩ i).hasDerivWithinAt (s:=Ici s)
    simpa only [ClearanceAdmission.actualCommand,ite_true,hs.2] using hd
  · intro s hs i
    have hd := (pending_deriv ex hb.2.1 hb.2.2 ⟨hs.1.le,hs.2⟩ i).hasDerivWithinAt (s:=Iic s)
    simpa only [ClearanceAdmission.actualCommand,Bool.false_eq_true,ite_false,hs.2,ite_true,prefixRate,prefixError] using hd

/-- This comparison restricts the recovered trajectory to the actual chosen
prefix endpoint. It uses no future zero or post-switch braking segment. -/
theorem position_to_decision (ex : BrakingExecution f rL qL rB qB) {σ : ℝ}
    (hσ : σ ∈ Icc (1/20:ℝ) (53/100)) : ∀ t ∈ Icc 0 σ, f t 0≤71/500 := by
  have hb : σ-1/20≤(12/25:ℝ) := by linarith [hσ.2]
  have hh := recovered_prefix_position_upper (show 0≤σ-1/20 by linarith [hσ.1])
    ex.loss ex.loss_rate_continuous ex.loss_rate (fun t ht => (ex.loss_target t ht).2)
    ex.position_initial ex.velocity_initial.2 ex.acceleration_initial.2
    (trajectory_restrict ex.brake hb) (ex.brake_rate_continuous.mono (Icc_subset_Icc_right hb))
    (fun s hs => (ex.brake_rate s ⟨hs.1,hs.2.trans hb⟩).1)
    (fun s hs => (ex.brake_target s ⟨hs.1,hs.2.trans hb⟩).2)
  simpa only [add_sub_cancel] using hh

end LeanControls.ConstructedHandoff
