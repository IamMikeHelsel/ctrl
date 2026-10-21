import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

set_option autoImplicit false
namespace R01Protocol

/- Abstract reducer, not packet authentication or the physical completion barrier.
   oracleCompletedTail is true completion of the current reference history, not a
   delivered completion packet. New isolated research, no approved Challenge. -/
structure State where
  watermark : Nat
  goal : Int
  busy : Bool
  deriving DecidableEq

inductive Event where
  | observe (sample : Int)
  | revise (authenticated : Bool) (version : Nat) (goal : Int)
  | oracleCompletedTail
  deriving DecidableEq

def step (s : State) : Event → State
  | .observe _ => s
  | .oracleCompletedTail => { s with busy := false }
  | .revise auth v g =>
      if auth && !s.busy && decide (s.watermark < v) then
        { watermark := v, goal := g, busy := true }
      else { s with watermark := max s.watermark (if auth then v else 0) }

def run (s : State) : List Event → State
  | [] => s
  | p :: ps => run (step s p) ps

theorem observation_preserves (s : State) (y : Int) : step s (.observe y) = s := rfl

theorem watermark_step (s : State) (p : Event) :
    s.watermark ≤ (step s p).watermark := by
  cases p with
  | observe y => exact Nat.le_refl _
  | oracleCompletedTail => exact Nat.le_refl _
  | revise auth v g =>
    simp only [step]
    split
    · rename_i h
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
      exact Nat.le_of_lt h.2
    · exact Nat.le_max_left _ _

theorem watermark_run (s : State) (ps : List Event) :
    s.watermark ≤ (run s ps).watermark := by
  induction ps generalizing s with
  | nil => exact Nat.le_refl _
  | cons p ps ih => exact Nat.le_trans (watermark_step s p) (ih (step s p))

theorem busy_revision_preserves_goal (s : State) (hs : s.busy = true)
    (auth : Bool) (v : Nat) (g : Int) :
    (step s (.revise auth v g)).goal = s.goal := by
  simp [step, hs]

theorem stale_revision_preserves_goal (s : State) (auth : Bool) (v : Nat) (g : Int)
    (hv : v ≤ s.watermark) : (step s (.revise auth v g)).goal = s.goal := by
  have hn : ¬ s.watermark < v := Nat.not_lt.mpr hv
  simp [step, hn]

#print axioms observation_preserves
#print axioms watermark_step
#print axioms watermark_run
#print axioms busy_revision_preserves_goal
#print axioms stale_revision_preserves_goal
end R01Protocol
