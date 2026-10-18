module
public import ConstructiveClock
public import LeanControls.UncertainLag
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.ConstructiveHold
open Set Filter DigitalHold

def paste (f g : ℝ → State) (T t : ℝ) : State := if t ≤ T then f t else g t

theorem paste_before (f g : ℝ → State) {T t : ℝ} (ht : t ≤ T) : paste f g T t=f t := by
  simp [paste,ht]

theorem paste_after {f g : ℝ → State} {T t : ℝ} (he : f T=g T) (ht : T ≤ t) : paste f g T t=g t := by
  by_cases hh : t ≤ T
  · have htt : t=T := le_antisymm hh ht; simp [paste,htt,he]
  · simp [paste,hh]

theorem paste_continuous {f g : ℝ → State} {T H : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hg : Continuous g) (he : f T=g T) :
    ContinuousOn (paste f g T) (Icc 0 H) := by
  apply ContinuousOn.if
  · intro t ht
    have hh : t=T := by simpa only [show {s : ℝ | s≤T}=Iic T from rfl,frontier_Iic,mem_singleton_iff] using ht.2
    simpa [hh] using he
  · apply hf.mono
    intro t ht
    exact ⟨ht.1.1,by simpa only [show {s : ℝ | s≤T}=Iic T from rfl,closure_Iic,mem_Iic] using ht.2⟩
  · exact hg.continuousOn

theorem paste_right_old {f g : ℝ → State} {T t d : ℝ} {i : Fin 3}
    (ht : t<T) (hf : HasDerivWithinAt (fun s => f s i) d (Ici t) t) :
    HasDerivWithinAt (fun s => paste f g T s i) d (Ici t) t := by
  apply hf.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with s hs
    simp [paste,hs.le]
  · simp [paste,ht.le]

theorem paste_left_old {f g : ℝ → State} {T t d : ℝ} {i : Fin 3}
    (ht : t≤T) (hf : HasDerivWithinAt (fun s => f s i) d (Iic t) t) :
    HasDerivWithinAt (fun s => paste f g T s i) d (Iic t) t := by
  apply hf.congr_of_mem
  · intro s hs; simp [paste,hs.trans ht]
  · exact le_rfl

theorem paste_right_new {f g : ℝ → State} {T t d : ℝ} {i : Fin 3}
    (ht : T≤t) (he : f T=g T) (hg : HasDerivAt (fun s => g s i) d t) :
    HasDerivWithinAt (fun s => paste f g T s i) d (Ici t) t := by
  apply hg.hasDerivWithinAt.congr_of_mem
  · intro s hs; rw [paste_after he (ht.trans hs)]
  · exact le_rfl

theorem paste_left_new {f g : ℝ → State} {T t d : ℝ} {i : Fin 3}
    (ht : T<t) (hg : HasDerivAt (fun s => g s i) d t) :
    HasDerivWithinAt (fun s => paste f g T s i) d (Iic t) t := by
  apply (hg.congr_of_eventuallyEq ?_).hasDerivWithinAt
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp [paste,not_le_of_gt hs]

def cellCommand (m : State) (ε : ℕ → State) (f : ℝ → State) (n : ℕ) : ℝ :=
  clip (command (ClearanceAdmission.center m) (measure m ε f (n+1)))

def phase (m : State) (R δ : ℕ → ℝ) (ε : ℕ → State) (f : ℝ → State) (n : ℕ) (t : ℝ) : State :=
  UncertainLag.heldSolution (R (n+1)) (t-grid (n+1)) (cellCommand m ε f n+δ (n+1)) (f (grid (n+1)))

theorem phase_initial (m : State) (R δ : ℕ → ℝ) (ε : ℕ → State) (f : ℝ → State) (n : ℕ) :
    phase m R δ ε f n (grid (n+1))=f (grid (n+1)) := by
  simp [phase,UncertainLag.exact_initial]

theorem phase_ode (m : State) {R : ℕ → ℝ} (δ : ℕ → ℝ) (ε : ℕ → State)
    (f : ℝ → State) (n : ℕ) (hr : R (n+1)≠0) (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => phase m R δ ε f n s i)
      (rhs (R (n+1)) (cellCommand m ε f n) (δ (n+1)) (phase m R δ ε f n t) i) t := by
  simpa [phase,rhs,Function.comp_def] using
    (UncertainLag.exact_ode hr (cellCommand m ε f n+δ (n+1)) (t-grid (n+1))
      (f (grid (n+1))) i).comp t ((hasDerivAt_id t).sub_const (grid (n+1)))

theorem phase_continuous (m : State) {R : ℕ → ℝ} (δ : ℕ → ℝ) (ε : ℕ → State)
    (f : ℝ → State) (n : ℕ) (hr : R (n+1)≠0) : Continuous (phase m R δ ε f n) :=
  continuous_pi fun i => continuous_iff_continuousAt.mpr fun t =>
    (phase_ode m δ ε f n hr t i).continuousAt

/-- The recursive function extends only from an already generated prefix.
The input sample is at n*h; the new cell starts at (n+1)*h. -/
def state (m : State) (g : ℝ → State) (R δ : ℕ → ℝ) (ε : ℕ → State) : ℕ → ℝ → State
  | 0 => g
  | n+1 => paste (state m g R δ ε n) (phase m R δ ε (state m g R δ ε n) n) (grid (n+1))

theorem state_step_before (m : State) (g : ℝ → State) (R δ : ℕ → ℝ) (ε : ℕ → State)
    (n : ℕ) {t : ℝ} (ht : t ≤ grid (n+1)) :
    state m g R δ ε (n+1) t=state m g R δ ε n t := paste_before _ _ ht

theorem state_prefix (m : State) (g : ℝ → State) (R δ : ℕ → ℝ) (ε : ℕ → State)
    (n : ℕ) {t : ℝ} (ht : t ≤ h) : state m g R δ ε n t=g t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [state_step_before m g R δ ε n (show t ≤ grid (n+1) by
      rw [grid_succ]; linarith [grid_nonneg n])]
    exact ih

def node (m : State) (g : ℝ → State) (R δ : ℕ → ℝ) (ε : ℕ → State) : ℕ → State
  | 0 => g 0
  | n+1 => state m g R δ ε n (grid (n+1))

theorem state_at_node (m : State) (g : ℝ → State) (R δ : ℕ → ℝ) (ε : ℕ → State) (n : ℕ) :
    state m g R δ ε n (grid n)=node m g R δ ε n := by
  cases n with
  | zero => simp [state,node,grid]
  | succ n => exact state_step_before m g R δ ε n le_rfl

/-- The endpoint recurrence depends on the two previous physical nodes.
The first reading is fixed by m; later readings add the supplied sensor error. -/
theorem node_recurrence (m : State) (g : ℝ → State) (R δ : ℕ → ℝ) (ε : ℕ → State) (n : ℕ) :
    node m g R δ ε (n+2)=UncertainLag.heldSolution (R (n+1)) h
      (clip (command (ClearanceAdmission.center m)
        (if n=0 then m else fun i => node m g R δ ε n i+ε n i))+δ (n+1))
      (node m g R δ ε (n+1)) := by
  change paste (state m g R δ ε n) (phase m R δ ε (state m g R δ ε n) n)
    (grid (n+1)) (grid (n+2)) = _
  rw [paste_after (phase_initial m R δ ε (state m g R δ ε n) n).symm
    (grid_strict.monotone (by omega))]
  have htime : grid (n+2)-grid (n+1)=h := by rw [show n+2=(n+1)+1 by omega,grid_succ]; ring
  simp only [phase,htime,cellCommand,measure,state_at_node,node]

end LeanControls.ConstructiveHold
