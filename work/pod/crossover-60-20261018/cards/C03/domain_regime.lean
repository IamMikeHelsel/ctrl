import Mathlib.Tactic
namespace C03Regime
/-- This scalar premise is the integrated jerk lower bound for terminal velocity zero. -/
theorem stop_after_half (T : ℝ) (hT : 0 ≤ T)
    (hv : (2601/8000 : ℝ)+(51/20)*T-5*T^2 ≤ 0) : 1/2 < T := by
  by_contra h
  have hprod : 0 ≤ T*(1/2-T) := mul_nonneg hT (by linarith)
  nlinarith

theorem optimized_alpha_regime (T : ℝ) (hT : 1/2 < T) :
    1/20 ≤ (T+117/400)/2 ∧ (T+117/400)/2 ≤ T-1/40 := by
  constructor <;> linarith

#print axioms stop_after_half
#print axioms optimized_alpha_regime
end C03Regime
