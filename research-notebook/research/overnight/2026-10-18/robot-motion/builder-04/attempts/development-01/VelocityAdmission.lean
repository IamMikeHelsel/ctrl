import VelocityGuard
import TimedAdmission

namespace RobotMotion.VelocityAdmission
open AccelerationAdmission

/-- Add sufficient velocity admission to the existing A/J/deadline contract.
The old checker and finite-candidate interface remain unchanged. -/
def checkVelocityTimedCandidate (h V A J c D : ℚ) (es : List QEvent)
    (delta tau : ℚ) : Bool :=
  checkTimedCandidate h A J c D es delta tau &&
    checkVelocity h V c (es++[(tau,delta)])

def chooseVelocityExecution (h V A J c D : ℚ) (es : List QEvent)
    (delta : ℚ) : List ℚ → Option ℚ
  | [] => none
  | tau::rest => if checkVelocityTimedCandidate h V A J c D es delta tau then some tau
      else chooseVelocityExecution h V A J c D es delta rest

lemma chosen_velocity_is_checked {h V A J c D delta tau : ℚ} {es : List QEvent}
    {candidates : List ℚ}
    (hc : chooseVelocityExecution h V A J c D es delta candidates = some tau) :
    tau ∈ candidates ∧ checkVelocityTimedCandidate h V A J c D es delta tau = true := by
  induction candidates with
  | nil => simp [chooseVelocityExecution] at hc
  | cons u rest ih =>
    by_cases hb : checkVelocityTimedCandidate h V A J c D es delta u = true
    · simp [chooseVelocityExecution,hb] at hc
      subst tau
      exact ⟨by simp,hb⟩
    · simp [chooseVelocityExecution,hb] at hc
      obtain ⟨hm,hv⟩ := ih hc
      exact ⟨by simp [hm],hv⟩

/-- This is exact rejection of the supplied finite tests, not proof that no
safe velocity trajectory or execution time exists. -/
lemma choose_velocity_none_iff (h V A J c D : ℚ) (es : List QEvent)
    (delta : ℚ) (candidates : List ℚ) :
    chooseVelocityExecution h V A J c D es delta candidates = none ↔
      ∀ tau ∈ candidates, checkVelocityTimedCandidate h V A J c D es delta tau = false := by
  induction candidates with
  | nil => simp [chooseVelocityExecution]
  | cons u rest ih =>
    by_cases hb : checkVelocityTimedCandidate h V A J c D es delta u = true
    · simp [chooseVelocityExecution,hb]
    · simp [chooseVelocityExecution,hb,ih]

noncomputable section

/-- A selected candidate has all three reference derivative bounds, preserves
its issued prefix and reaches reference rest by the declared deadline.
This is not a physical-state, sampling or robot-hardware contract. -/
theorem chosen_velocity_reference_contract {h V A J c D delta tau : ℚ} {es : List QEvent}
    {candidates : List ℚ}
    (hc : chooseVelocityExecution h V A J c D es delta candidates = some tau) (g0 : ℝ) :
    c ≤ tau ∧
    (∀ t : ℝ, (c:ℝ) ≤ t → |velocity (h:ℝ) (realEvents (es++[(tau,delta)])) t| ≤ (V:ℝ)) ∧
    (∀ t : ℝ, (c:ℝ) ≤ t → |acceleration (h:ℝ) (realEvents (es++[(tau,delta)])) t| ≤ (A:ℝ)) ∧
    (∀ t : ℝ, (c:ℝ) ≤ t → |jerk (h:ℝ) (realEvents (es++[(tau,delta)])) t| ≤ (J:ℝ)) ∧
    (∀ t : ℝ, t ≤ (tau:ℝ) → referenceJet g0 (h:ℝ) (realEvents (es++[(tau,delta)])) t =
      referenceJet g0 (h:ℝ) (realEvents es) t) ∧
    (∀ t : ℝ, (D:ℝ) ≤ t →
      position g0 (h:ℝ) (realEvents (es++[(tau,delta)])) t =
        g0+((realEvents (es++[(tau,delta)])).map Prod.snd).sum ∧
      velocity (h:ℝ) (realEvents (es++[(tau,delta)])) t = 0 ∧
      acceleration (h:ℝ) (realEvents (es++[(tau,delta)])) t = 0 ∧
      jerk (h:ℝ) (realEvents (es++[(tau,delta)])) t = 0) := by
  obtain ⟨_,hb⟩ := chosen_velocity_is_checked hc
  have hp := Bool.and_eq_true.mp hb
  have hold : chooseExecution h A J c D es delta [tau] = some tau := by
    simp [chooseExecution,hp.1]
  obtain ⟨hct,hacc,hjerk,hpre,hrest⟩ := chosen_reference_contract hold g0
  exact ⟨hct,(checkVelocity_real_sound hp.2).2.2,hacc,hjerk,hpre,hrest⟩

end
end RobotMotion.VelocityAdmission
