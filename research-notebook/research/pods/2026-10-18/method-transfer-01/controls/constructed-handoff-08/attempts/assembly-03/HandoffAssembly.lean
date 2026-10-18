module
public import HandoffPrefix
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.ConstructedHandoff
open Set Filter DigitalHold ConstructiveHold DetectorBridge DetectorSampling

def join (f v : ℝ → State) (σ t : ℝ) : State := if t≤σ then f t else v (t-σ)

theorem join_before (f v : ℝ → State) {σ t : ℝ} (ht : t≤σ) : join f v σ t=f t := by simp [join,ht]

theorem join_after {f v : ℝ → State} {σ t : ℝ} (he : f σ=v 0) (ht : σ≤t) :
    join f v σ t=v (t-σ) := by
  by_cases hh : t≤σ
  · have h : t=σ := le_antisymm hh ht; simp [join,h,he]
  · simp [join,hh]

theorem join_local {f v : ℝ → State} {σ s : ℝ} (he : f σ=v 0) (hs : 0≤s) :
    join f v σ (σ+s)=v s := by simpa using join_after he (show σ≤σ+s by linarith)

theorem join_prefix {f v : ℝ → State} {σ t : ℝ}
    (hp : ∀ s ∈ Icc 0 h, v s=f (σ+s)) (ht : t ∈ Icc 0 (σ+h)) : join f v σ t=f t := by
  by_cases hh : t≤σ
  · exact join_before f v hh
  · have he : f σ=v 0 := by simpa using (hp 0 ⟨le_rfl,by norm_num⟩).symm
    rw [join_after he (le_of_not_ge hh),hp (t-σ) ⟨by linarith,by linarith [ht.2]⟩]
    congr 1; ring

theorem join_continuous {f v : ℝ → State} {σ L : ℝ}
    (hf : ContinuousOn f (Icc 0 σ)) (hv : ContinuousOn v (Icc 0 L)) (he : f σ=v 0) :
    ContinuousOn (join f v σ) (Icc 0 (σ+L)) := by
  apply ContinuousOn.if
  · intro t ht
    have hh : t=σ := by simpa only [show {s : ℝ | s≤σ}=Iic σ from rfl,frontier_Iic,mem_singleton_iff] using ht.2
    simp [hh,he]
  · apply hf.mono
    intro t ht
    exact ⟨ht.1.1,by simpa only [show {s : ℝ | s≤σ}=Iic σ from rfl,closure_Iic,mem_Iic] using ht.2⟩
  · have hc : ContinuousOn (fun t => v (t-σ)) (Icc σ (σ+L)) :=
      hv.comp (continuous_id.sub continuous_const).continuousOn (by intro t ht; exact ⟨by linarith [ht.1],by linarith [ht.2]⟩)
    apply hc.mono
    intro t ht
    refine ⟨?_,ht.1.2⟩
    have heq : {s : ℝ | ¬s≤σ}=Ioi σ := by ext s; simp
    simpa only [heq,closure_Ioi,mem_Ici] using ht.2

theorem join_old_deriv {f v : ℝ → State} {σ t d : ℝ} {i : Fin 3}
    (hp : ∀ s ∈ Icc 0 h, v s=f (σ+s)) (ht : t ∈ Ioo 0 (σ+h))
    (hd : HasDerivAt (fun s => f s i) d t) : HasDerivAt (fun s => join f v σ s i) d t := by
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact congrArg (fun z => z i) (join_prefix hp ⟨hs.1.le,hs.2.le⟩)

theorem join_right_deriv {f v : ℝ → State} {σ s d : ℝ} {i : Fin 3}
    (he : f σ=v 0) (hs : 0≤s)
    (hd : HasDerivWithinAt (fun u => v u i) d (Ici s) s) :
    HasDerivWithinAt (fun t => join f v σ t i) d (Ici (σ+s)) (σ+s) := by
  have hh := hd.comp_of_eq (σ+s) ((hasDerivAt_id (σ+s)).sub_const σ).hasDerivWithinAt
    (s := Ici (σ+s)) (by intro t ht; change s≤t-σ; change σ+s≤t at ht; linarith) (by ring : s=σ+s-σ)
  have hh' : HasDerivWithinAt (fun t => v (t-σ) i) d (Ici (σ+s)) (σ+s) := by
    simpa only [Function.comp_def,id_eq,mul_one] using hh
  apply hh'.congr_of_mem
  · intro t ht; exact congrArg (fun z => z i) (join_after (t:=t) he (by change σ+s≤t at ht; linarith))
  · exact le_rfl

theorem join_left_deriv {f v : ℝ → State} {σ s d : ℝ} {i : Fin 3}
    (he : f σ=v 0) (hs : 0<s)
    (hd : HasDerivWithinAt (fun u => v u i) d (Iic s) s) :
    HasDerivWithinAt (fun t => join f v σ t i) d (Iic (σ+s)) (σ+s) := by
  have hh := hd.comp_of_eq (σ+s) ((hasDerivAt_id (σ+s)).sub_const σ).hasDerivWithinAt
    (s := Iic (σ+s)) (by intro t ht; change t-σ≤s; change t≤σ+s at ht; linarith) (by ring : s=σ+s-σ)
  have hh' : HasDerivWithinAt (fun t => v (t-σ) i) d (Iic (σ+s)) (σ+s) := by
    simpa only [Function.comp_def,id_eq,mul_one] using hh
  apply hh'.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show σ<σ+s by linarith))] with t ht
    exact congrArg (fun z => z i) (join_after (t:=t) he ht.le)
  · exact congrArg (fun z => z i) (join_after (t:=σ+s) he (by linarith))

def hold (f : ℝ → State) (m : ℕ → State) (k N : ℕ) (R δ : ℕ → ℝ) (ε : ℕ → State) : ℝ → State :=
  state (m k) (pending f (grid k)) R δ ε (N-1)
def trajectory (f : ℝ → State) (m : ℕ → State) (k N : ℕ) (R δ : ℕ → ℝ) (ε : ℕ → State) : ℝ → State :=
  join f (hold f m k N R δ ε) (grid k)

def newReadings (m : ℕ → State) (v : ℝ → State) (k : ℕ) (ε : ℕ → State) (j : ℕ) : State :=
  if j≤k then m j else measure (m k) ε v (j-k)

theorem new_readings_first {m : ℕ → State} {v : ℝ → State} {k : ℕ} {ε : ℕ → State}
    (hk : First m k) : First (newReadings m v k ε) k :=
  first_prefix_stable hk (fun j hj => by simp [newReadings,hj])

theorem schedule_reading_link (m : ℕ → State) (v : ℝ → State) (k j : ℕ) (ε : ℕ → State) :
    newReadings m v k ε (k+j)=(ConstructiveHold.schedule (m k) ε v).measurement j := by
  by_cases hj : j=0
  · subst j; simp [newReadings,ConstructiveHold.schedule,measure]
  · have hk : ¬k+j≤k := by omega
    simp [newReadings,hk,ConstructiveHold.schedule]

theorem translated_clocks (k j : ℕ) : grid k+grid j=grid (k+j) ∧
    grid k+h+grid j=grid (k+j+1) ∧ grid k+h+grid (j+1)-(grid k+grid j)=1/1000 := by
  refine ⟨?_,?_,?_⟩ <;> simp [grid,Nat.cast_add] <;> ring

structure Assembly (f : ℝ → State) (rL qL rB qB : ℝ → ℝ) (m : ℕ → State)
    (k N : ℕ) (R δ : ℕ → ℝ) (ε : ℕ → State) : Prop where
  first : First m k
  bounds : 605≤k ∧ k≤1058
  continuous : ContinuousOn (trajectory f m k N R δ ε) (Icc 0 (grid k+grid N))
  prefix_eq : ∀ t ∈ Icc 0 (grid k+h), trajectory f m k N R δ ε t=f t
  local_match : ∀ s ∈ Icc 0 (grid N), trajectory f m k N R δ ε (grid k+s)=hold f m k N R δ ε s
  execution : ClearanceAdmission.Execution (grid N) h (m k) (hold f m k N R δ ε)
    (field (prefixRate rB (grid k)) R) (field (prefixError qB (grid k)) δ)
    stamp (readings (m k) ε (hold f m k N R δ ε))
  schedule : ClearanceAdmission.IsSchedule (grid N) h (schedule (m k) ε (hold f m k N R δ ε))
    stamp (readings (m k) ε (hold f m k N R δ ε))
  first_reading : (ConstructiveHold.schedule (m k) ε (hold f m k N R δ ε)).measurement 0=m k
  safety : ∀ t ∈ Icc 0 (grid k+grid N), trajectory f m k N R δ ε t 0≤3013722449/20100000000
  loss_ode : ∀ t ∈ Ioo (0:ℝ) (1/20), ∀ i : Fin 3,
    HasDerivAt (fun s => trajectory f m k N R δ ε s i)
      (![f t 1,f t 2,rL t*(qL t-f t 2)] i) t
  brake_ode : ∀ t ∈ Ioo (1/20:ℝ) (grid k+h), ∀ i : Fin 3,
    HasDerivAt (fun s => trajectory f m k N R δ ε s i)
      (![f t 1,f t 2,rB (t-1/20)*(qB (t-1/20)-f t 2)] i) t

theorem assemble {f : ℝ → State} {rL qL rB qB : ℝ → ℝ} {m : ℕ → State}
    (ex : BrakingExecution f rL qL rB qB) (hm : Readings f m) {k N : ℕ}
    (hk : k≤1058) (hf : First m k) (hN : 2≤N) {R δ : ℕ → ℝ} {ε : ℕ → State}
    (hr : ∀ n, 1≤n → 8≤R n ∧ R n≤12) (hd : ∀ n, 1≤n → |δ n|≤1/100)
    (he : ∀ n, |ε n 0|≤1/1000 ∧ |ε n 1|≤1/100 ∧ |ε n 2|≤1/20) :
    Assembly f rL qL rB qB m k N R δ ε := by
  have hb := decision_bounds ex hm hk hf.1
  have hp := pending_execution ex hm hk hf.1
  have hc := ConstructiveHold.continuation hp hr hd he N hN hf.1
  have hpre : ∀ s ∈ Icc 0 h, hold f m k N R δ ε s=f (grid k+s) := hc.1
  have heq : f (grid k)=hold f m k N R δ ε 0 := by simpa using (hpre 0 ⟨le_rfl,by norm_num⟩).symm
  refine ⟨hf,⟨hb.1,hk⟩,?_,?_,?_,hc.2.1,hc.2.2.1,hc.2.2.2.1,?_,?_,?_⟩
  · exact join_continuous (ex.continuous.mono (Icc_subset_Icc_right (by linarith [hb.2.2]))) hc.2.1.continuous heq
  · intro t ht; exact join_prefix hpre ht
  · intro s hs; exact join_local heq hs.1
  · intro t ht
    by_cases hs : t≤grid k
    · rw [show trajectory f m k N R δ ε t=f t from join_before _ _ hs]
      have hh := position_to_decision ex ⟨hb.2.1.le,by linarith [hb.2.2]⟩ t ⟨ht.1,hs⟩
      linarith
    · have hh := hc.2.2.2.2 (t-grid k) ⟨by linarith,by linarith [ht.2]⟩
      rw [show trajectory f m k N R δ ε t=hold f m k N R δ ε (t-grid k) from join_after heq (le_of_not_ge hs)]
      convert hh using 1 <;> norm_num [hold]
  · intro t ht i
    exact join_old_deriv hpre ⟨ht.1,ht.2.trans (hb.2.1.trans_le (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤h)))⟩ (ex.loss.ode t ht i)
  · intro t ht i
    exact join_old_deriv hpre ⟨by linarith [ht.1],ht.2⟩ (recovered_deriv ex ⟨ht.1,ht.2.trans hb.2.2⟩ i)

theorem exists_assembly {f : ℝ → State} {rL qL rB qB : ℝ → ℝ} {m : ℕ → State}
    (ex : BrakingExecution f rL qL rB qB) (hm : Readings f m) (N : ℕ) (hN : 2≤N)
    {R δ : ℕ → ℝ} {ε : ℕ → State}
    (hr : ∀ n, 1≤n → 8≤R n ∧ R n≤12) (hd : ∀ n, 1≤n → |δ n|≤1/100)
    (he : ∀ n, |ε n 0|≤1/1000 ∧ |ε n 1|≤1/100 ∧ |ε n 2|≤1/20) :
    ∃ k, Assembly f rL qL rB qB m k N R δ ε := by
  obtain ⟨k,hk,hg,hfirst,_⟩ := finite_first_guard ex hm
  exact ⟨k,assemble ex hm hk ⟨hg,hfirst⟩ hN hr hd he⟩

section Consequences
variable {f : ℝ → State} {rL qL rB qB : ℝ → ℝ} {m : ℕ → State}
  {k N : ℕ} {R δ : ℕ → ℝ} {ε : ℕ → State}
variable (a : Assembly f rL qL rB qB m k N R δ ε)
include a

theorem assembly_join_value : f (grid k)=hold f m k N R δ ε 0 := by
  have hp := a.prefix_eq (grid k) ⟨grid_nonneg k,by norm_num⟩
  have hl := a.local_match 0 ⟨le_rfl,grid_nonneg N⟩
  simp only [add_zero] at hl
  exact hp.symm.trans hl

theorem absolute_right {s : ℝ} (hs : s ∈ Ico 0 (grid N)) (i : Fin 3) :
    HasDerivWithinAt (fun t => trajectory f m k N R δ ε t i)
      (rhs (field (prefixRate rB (grid k)) R true s)
        (ClearanceAdmission.actualCommand h (ClearanceAdmission.center (m k))
          (readings (m k) ε (hold f m k N R δ ε)) true s)
        (field (prefixError qB (grid k)) δ true s) (hold f m k N R δ ε s) i)
      (Ici (grid k+s)) (grid k+s) :=
  join_right_deriv (assembly_join_value a) hs.1 (a.execution.right_ode s hs i)

theorem absolute_left {s : ℝ} (hs : s ∈ Ioc 0 (grid N)) (i : Fin 3) :
    HasDerivWithinAt (fun t => trajectory f m k N R δ ε t i)
      (rhs (field (prefixRate rB (grid k)) R false s)
        (ClearanceAdmission.actualCommand h (ClearanceAdmission.center (m k))
          (readings (m k) ε (hold f m k N R δ ε)) false s)
        (field (prefixError qB (grid k)) δ false s) (hold f m k N R δ ε s) i)
      (Iic (grid k+s)) (grid k+s) :=
  join_left_deriv (assembly_join_value a) hs.1 (a.execution.left_ode s hs i)

theorem arrived_first_and_stable {m' : ℕ → State} (he : ∀ j≤k, m' j=m j) :
    First m' k ∧ ∀ j<k, grid j+h<grid k+h := by
  exact ⟨first_prefix_stable a.first he,fun j hj => by linarith [grid_strict hj]⟩

theorem actual_readings (hm : Readings f m)
    (he : ∀ n, |ε n 0|≤1/1000 ∧ |ε n 1|≤1/100 ∧ |ε n 2|≤1/20)
    (j : ℕ) (hj : j≤k+N) :
    SensorBox (trajectory f m k N R δ ε (grid j))
      (newReadings m (hold f m k N R δ ε) k ε j) := by
  by_cases hpre : j≤k
  · rw [newReadings,if_pos hpre,a.prefix_eq (grid j) ⟨grid_nonneg j,by
      have hh := grid_strict.monotone hpre; linarith⟩]
    exact hm j (by have hk := a.bounds.2; omega)
  · have hn : j-k≠0 := by omega
    have hg : grid j=grid k+grid (j-k) := by
      rw [(translated_clocks k (j-k)).1,Nat.add_sub_of_le (le_of_not_ge hpre)]
    have hmch := a.local_match (grid (j-k)) ⟨grid_nonneg _,grid_strict.monotone (by omega)⟩
    rw [newReadings,if_neg hpre,measure,if_neg hn,hg,hmch]
    simpa [SensorBox] using he (j-k)

end Consequences

end LeanControls.ConstructedHandoff
