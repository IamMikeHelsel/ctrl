import Mathlib.Tactic
namespace R03Domain
/-- t is the linearization instant; publication and dispatch occur afterward.
The estimate is from an earlier read, whose age is bounded separately. -/
theorem robust_delivery_order {read commit execution estimate target ec ee age tail dispatch : ℝ}
    (hr : read ≤ estimate + ec) (hc : commit ≤ read + age)
    (he : target - ee ≤ execution)
    (gate : estimate + ec + age + tail + dispatch ≤ target - ee) :
    commit + tail + dispatch ≤ execution := by linarith
/-- Offset uncertainty grows over a validated horizon under a drift bound. -/
theorem drift_margin {err initial rate elapsed horizon : ℝ}
    (he : |err| ≤ initial + rate * elapsed) (hr : 0 ≤ rate)
    (ht : elapsed ≤ horizon) : |err| ≤ initial + rate * horizon := by nlinarith
/-- These are exactly the four arithmetic inequalities required by source timeOK.
All times here must already use the single reference-time coordinate. -/
theorem ideal_time_contract {request completion commit execution dispatch : ℝ}
    (hreq : request ≤ completion) (hcomp : completion ≤ commit)
    (hd : 0 ≤ dispatch) (he : commit + dispatch ≤ execution) :
    request ≤ completion ∧ completion ≤ commit ∧ 0 ≤ dispatch ∧
      commit + dispatch ≤ execution := ⟨hreq,hcomp,hd,he⟩
/-- A previously valid clock read need not remain valid when data are unchanged. -/
theorem old_read_can_expire :
    (57/100 : ℝ) + 1/100 ≤ 31/50 ∧
    ¬ ((57/100 : ℝ) + 1/10 + 1/100 ≤ 31/50) := by norm_num
/-- Equality at the atomic step, rather than merely at validation, transports P. -/
theorem atomic_snapshot_transport {Snapshot : Type*} {P : Snapshot → Prop}
    {pending live : Snapshot} (checked : P pending) (same : live = pending) : P live := by
  simpa only [same] using checked
/-- The complete state need not be determined by a version projection. -/
theorem version_only_insufficient :
    (7, (0 : ℤ)).1 = (7, (1 : ℤ)).1 ∧ (7, (0 : ℤ)) ≠ (7, (1 : ℤ)) := by decide
#print axioms robust_delivery_order
#print axioms drift_margin
#print axioms ideal_time_contract
#print axioms old_read_can_expire
#print axioms atomic_snapshot_transport
#print axioms version_only_insufficient
end R03Domain
