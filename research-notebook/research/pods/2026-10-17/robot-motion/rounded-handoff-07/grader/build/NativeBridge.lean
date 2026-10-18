import NativeData
import RoundedHandoff

noncomputable section
namespace NativeRational
open Set
open LeanControls
open LeanControls.UncertainLag (State)
open LeanControls.VariableResponse LeanControls.RobustHold
open LeanControls.TrackingReplan LeanControls.ScaledTracking LeanControls.RoundedHandoff

def pieceAt (xs : List Piece) (k : ℕ) : Piece :=
  xs[k]?.getD ⟨0,0,0,0,0,0⟩

theorem pieceAt_eq_getElem (xs : List Piece) (k : ℕ) (hk : k < xs.length) :
    pieceAt xs k = xs[k] := by simp [pieceAt, List.getElem?_eq_getElem hk]

theorem check_all {H : ℚ} {xs : List Piece} (h : check H xs = true) :
    ∀ s ∈ xs, SegmentOK s := by
  cases xs with
  | nil => simp [check] at h
  | cons s rest =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa only [List.all_eq_true, decide_eq_true_eq] using h.1.1.2

theorem check_chain {H : ℚ} {xs : List Piece} (h : check H xs = true) :
    chainOK xs = true := by
  cases xs with
  | nil => simp [chainOK]
  | cons s rest =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.2

theorem chain_get {xs : List Piece} (h : chainOK xs = true)
    (k : ℕ) (hk : k+1 < xs.length) : JoinOK xs[k] xs[k+1] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons s rest ih =>
    cases rest with
    | nil => simp at hk
    | cons t rest =>
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
      cases k with
      | zero => simpa using h.1
      | succ k =>
        have hk' : k+1 < (t::rest).length := by simpa using hk
        simpa using ih h.2 k hk'

theorem check_segment {H : ℚ} {xs : List Piece} (h : check H xs = true)
    (k : ℕ) (hk : k < xs.length) : SegmentOK (pieceAt xs k) := by
  rw [pieceAt_eq_getElem xs k hk]
  exact check_all h _ (List.getElem_mem hk)

theorem check_join {H : ℚ} {xs : List Piece} (h : check H xs = true)
    (k : ℕ) (hk : k+1 < xs.length) : JoinOK (pieceAt xs k) (pieceAt xs (k+1)) := by
  rw [pieceAt_eq_getElem xs k (by omega), pieceAt_eq_getElem xs (k+1) hk]
  exact chain_get (check_chain h) k hk

def realState (s : Piece) : SmoothReplan.State := ⟨s.p,s.v,s.a⟩
def realDuration (xs : List Piece) (k : ℕ) : ℝ := duration (pieceAt xs k)
def realJerk (xs : List Piece) (k : ℕ) : ℝ := (pieceAt xs k).j
def realZ (xs : List Piece) (k : ℕ) : SmoothReplan.State := realState (pieceAt xs k)

theorem checked_duration {H : ℚ} {xs : List Piece} (h : check H xs = true)
    (k : ℕ) (hk : k < xs.length) : 0 ≤ realDuration xs k := by
  have hp := (check_segment h k hk).1
  dsimp [realDuration]
  exact_mod_cast hp.le

theorem checked_jerk {H : ℚ} {xs : List Piece} (h : check H xs = true)
    (k : ℕ) (hk : k < xs.length) : |realJerk xs k| ≤ 15/2 := by
  have hj := (check_segment h k hk).2
  dsimp [realJerk]
  have hc : ((|(pieceAt xs k).j| : ℚ) : ℝ) ≤ ((15/2:ℚ):ℝ) := by exact_mod_cast hj
  simpa using hc

theorem join_real {s t : Piece} (h : JoinOK s t) :
    ∀ i, |coordinates 0 (scaleState 10
      (reference (realState t) t.j 0 - reference (realState s) s.j (duration s))) i| ≤
        (allowance : ℝ) := by
  rcases h with ⟨_,h0,h1,h2⟩
  have hh0 : |(t.p:ℝ)-(endP s:ℝ)| ≤ (allowance:ℝ) := by exact_mod_cast h0
  have hh1 : |((t.p:ℝ)-(endP s:ℝ))+((t.v:ℝ)-(endV s:ℝ))/40| ≤ (allowance:ℝ) := by exact_mod_cast h1
  have hh2 : |((t.p:ℝ)-(endP s:ℝ))+((t.v:ℝ)-(endV s:ℝ))/20+((t.a:ℝ)-(endA s:ℝ))/1600| ≤ (allowance:ℝ) := by exact_mod_cast h2
  intro i
  fin_cases i
  all_goals simp [scaleState, reference, realState, SmoothReplan.position,
    SmoothReplan.velocity, SmoothReplan.acceleration, coordinates, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    pow_zero, pow_one, div_one]
  all_goals push_cast [endP, endV, endA] at hh0 hh1 hh2
  · convert hh0 using 1
  · convert hh1 using 1; congr 1; ring
  · convert hh2 using 1; congr 1; ring

theorem checked_jump {H : ℚ} {xs : List Piece} (h : check H xs = true)
    (k : ℕ) (hk : k+1 < xs.length) :
    ∀ i, |coordinates 0 (scaleState 10
      (reference (realZ xs (k+1)) (realJerk xs (k+1)) 0 -
       reference (realZ xs k) (realJerk xs k) (realDuration xs k))) i| ≤
        (allowance : ℝ) := join_real (check_join h k hk)

/-- The guard supplies the cubic durations, jerk bounds, and all reference jumps.
Only actual plant conditions and physical-state continuity remain premises. -/
theorem checked_cubic_tracking {H : ℚ} {xs : List Piece} (h : check H xs = true)
    {f : ℕ → ℝ → State} {r w : ℕ → ℝ → ℝ}
    (hf : ∀ k < xs.length, IsTrajectory (realDuration xs k) (r k)
      (fun t => physicalInput 10 (f k) (reference (realZ xs k) (realJerk xs k))
        (fun _ => realJerk xs k) t + w k t) (f k))
    (hrlo : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), 80 ≤ r k t)
    (hrhi : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), r k t ≤ 120)
    (hw : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), |w k t| ≤ 1/100)
    (hphysical : ∀ k, k+1 < xs.length → f (k+1) 0 = f k (realDuration xs k))
    (hi : ∀ i, |coordinates 0 (scaledError 10 (f 0)
      (reference (realZ xs 0) (realJerk xs 0)) 0) i| ≤ 41/320000) :
    ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), ∀ i,
      |coordinates 0 (scaledError 10 (f k)
        (reference (realZ xs k) (realJerk xs k)) t) i| ≤
          41/320000 + k*(allowance:ℝ) := by
  have result := finite_cubic_replans (N:=xs.length) (σ:=10)
    (R₀:=41/320000) (W:=1/100) (J:=15/2) (B:=fun _ => (allowance:ℝ))
    (by norm_num) (by norm_num) (by intro k; norm_num [allowance])
    (checked_duration h) hf (by simpa only [show (8:ℝ)*10=80 by norm_num] using hrlo)
    (by simpa only [show (12:ℝ)*10=120 by norm_num] using hrhi)
    hw (checked_jerk h) (by norm_num) hphysical (checked_jump h) hi
  simpa only [constant_radius] using result

/-- A bound on each local time, including both sides of every reference join.
The stored fixtures have at most 189 pieces, hence at most 188 joins. -/
theorem checked_position_tracking {H : ℚ} {xs : List Piece}
    (h : check H xs = true) (hlen : xs.length ≤ 189)
    {f : ℕ → ℝ → State} {r w : ℕ → ℝ → ℝ}
    (hf : ∀ k < xs.length, IsTrajectory (realDuration xs k) (r k)
      (fun t => physicalInput 10 (f k) (reference (realZ xs k) (realJerk xs k))
        (fun _ => realJerk xs k) t + w k t) (f k))
    (hrlo : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), 80 ≤ r k t)
    (hrhi : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), r k t ≤ 120)
    (hw : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), |w k t| ≤ 1/100)
    (hphysical : ∀ k, k+1 < xs.length → f (k+1) 0 = f k (realDuration xs k))
    (hi : ∀ i, |coordinates 0 (scaledError 10 (f 0)
      (reference (realZ xs 0) (realJerk xs 0)) 0) i| ≤ 41/320000) :
    ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k),
      |f k t 0 - reference (realZ xs k) (realJerk xs k) t 0| ≤
        41/320000 + 188/1000000000000000 := by
  intro k hk t ht
  have hc := checked_cubic_tracking h hf hrlo hrhi hw hphysical hi k hk t ht
  have he := (tracking_error_bounds (by norm_num : (0:ℝ)<10) hc).1
  have hkn : k ≤ 188 := by omega
  have hkr : (k:ℝ) ≤ 188 := by exact_mod_cast hkn
  exact he.trans (by norm_num [allowance]; linarith)

theorem certified_radius_below_target :
    (41/320000:ℝ) + 188/1000000000000000 < 1/5000 := by norm_num

end NativeRational
