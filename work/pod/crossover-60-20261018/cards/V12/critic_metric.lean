import Mathlib.Tactic
namespace V12Critic
-- Literal six Zhang rows for the projective homographies in critic_rank.json.
theorem indefinite_line (a b c d e f : ℝ)
    (h0 : b = 0) (h1 : a-c=0) (h2 : (5*b+4*e)/3=0)
    (h3 : (25*a+40*d+16*f)/9-c=0) (h4 : (5*b+4*d)/3=0)
    (h5 : a-(25*c+40*e+16*f)/9=0) :
    b=0 ∧ d=0 ∧ e=0 ∧ c=a ∧ f= -a := by
  refine ⟨h0, ?_, ?_, ?_, ?_⟩ <;> linarith
-- Positive definiteness implies both diagonal tests below.
theorem no_positive_metric (a f : ℝ) (h : f= -a) (ha : 0<a) (hf : 0<f) : False := by
  linarith
theorem line_attains (a : ℝ) :
    (25*a+16*(-a))/9-a=0 ∧ a-(25*a+16*(-a))/9=0 := by constructor <;> ring
-- A single homogeneous sign cannot make the whole board visible.
theorem straddling (s : ℝ) (hleft : 0 < s*(-7/10))
    (hright : 0 < s*(9/10)) : False := by nlinarith
end V12Critic
#print axioms V12Critic.indefinite_line
#print axioms V12Critic.no_positive_metric
#print axioms V12Critic.line_attains
#print axioms V12Critic.straddling
