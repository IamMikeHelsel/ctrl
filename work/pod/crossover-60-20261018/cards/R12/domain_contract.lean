import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

noncomputable section
namespace R12Domain

/-- Residual force must be bounded in the full coupled inertia metric, not per scalar model. -/
theorem coupled_acceleration_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E → E) (a r : E) (m B : ℝ) (hm : 0 < m)
    (hcoercive : m * ‖a‖^2 ≤ inner ℝ a (M a))
    (hdynamics : M a = r) (hr : ‖r‖ ≤ B) : ‖a‖ ≤ B / m := by
  rw [hdynamics] at hcoercive
  have hc := real_inner_le_norm a r
  have ha := norm_nonneg a
  have hb : 0 ≤ B := le_trans (norm_nonneg r) hr
  apply (le_div_iff₀ hm).2
  by_cases hz : ‖a‖ = 0
  · rw [hz]; simpa using hb
  · have hap : 0 < ‖a‖ := lt_of_le_of_ne ha (Ne.symm hz)
    have hx : m * ‖a‖ ≤ ‖r‖ := by nlinarith
    nlinarith

/-- Exact signed headroom after all generalized-force contributions have been added. -/
theorem total_force_budget_iff (act assist limit : ℝ) :
    |act + assist| ≤ limit ↔ -limit-assist ≤ act ∧ act ≤ limit-assist := by
  rw [abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

/-- A sufficient symmetric reserve; this is conservative when signs cancel. -/
theorem reserve_sufficient (act assist limit reserve : ℝ)
    (ha : |act| ≤ limit-reserve) (hb : |assist| ≤ reserve) :
    |act+assist| ≤ limit := by
  have ht := abs_add_le act assist
  linarith

/-- Keeping the old actuator bound alone cannot bound an additional input. -/
theorem unguarded_assist_counterexample :
    |(10:ℝ)| ≤ 12 ∧ |10+5| > (12:ℝ) := by norm_num

/-- The exact servo error forcing identity in each component after M qdd has been assembled.
Variables inertiaActual/inertiaReference are coupled matrix-vector products, not diagonal masses. -/
theorem coupled_error_identity (inertiaActual inertiaReference kp kv command q qd v vd
    biasAssist bias passive constraint : ℝ)
    (hdynamics : inertiaActual + bias = kp*(command-q)-kv*v+biasAssist+passive+constraint) :
    (inertiaActual-inertiaReference)+kv*(v-vd)+kp*(q-qd) =
    (biasAssist-bias)+passive+constraint-inertiaReference-kv*vd+kp*(command-qd) := by
  linarith

/-- Clamp-aware identity. clampResidual is delivered generalized actuator force minus
raw PD demand; it must not be omitted merely because one recorded trace did not saturate. -/
theorem coupled_error_with_clamp (inertiaActual inertiaReference kp kv command q qd v vd
    biasAssist bias passive constraint actuator clampResidual : ℝ)
    (hdynamics : inertiaActual + bias = actuator+biasAssist+passive+constraint)
    (hactuator : actuator = kp*(command-q)-kv*v+clampResidual) :
    (inertiaActual-inertiaReference)+kv*(v-vd)+kp*(q-qd) =
    (biasAssist-bias)+passive+constraint-inertiaReference-kv*vd+
      kp*(command-qd)+clampResidual := by
  rw [hactuator] at hdynamics
  linarith

/-- A causal velocity lead cancels the omitted velocity forcing, but not inertia,
friction, modeling error or hold error. -/
theorem velocity_lead_residual (kp kv lead vd command qd holdError : ℝ)
    (hg : kv = kp*lead) (hc : command = qd+lead*vd+holdError) :
    -kv*vd+kp*(command-qd) = kp*holdError := by
  rw [hg,hc]
  ring

lemma source_gain_ratio :
    (450:ℝ)/4500 = 1/10 ∧ (350:ℝ)/3500 = 1/10 ∧ (200:ℝ)/2000 = 1/10 := by
  norm_num

/-- Task-space Lipschitz and the same authoritative reference compose with tracking,
not merely a final-window sample. -/
theorem task_tube (actual reference goal : EuclideanSpace ℝ (Fin 3))
    (tracking referenceBudget tolerance : ℝ)
    (ht : dist actual reference ≤ tracking)
    (hr : dist reference goal ≤ referenceBudget)
    (hb : tracking+referenceBudget ≤ tolerance) : dist actual goal ≤ tolerance := by
  have h := dist_triangle actual reference goal
  linarith

#print axioms coupled_acceleration_bound
#print axioms total_force_budget_iff
#print axioms reserve_sufficient
#print axioms unguarded_assist_counterexample
#print axioms coupled_error_identity
#print axioms coupled_error_with_clamp
#print axioms velocity_lead_residual
#print axioms source_gain_ratio
#print axioms task_tube
end R12Domain
