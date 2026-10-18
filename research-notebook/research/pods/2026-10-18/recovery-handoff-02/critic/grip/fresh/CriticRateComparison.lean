import Recovery
namespace IndependentRecoveryCritic
-- q=-1, a=-2, actual rate r=2, lower rate k=1, b=1.
example : (2:ℝ)*(-1-(-2)) > -(1:ℝ)*((-2)+1) := by norm_num
example : ¬ ((2:ℝ)*(-1-(-2)) ≤ -(1:ℝ)*((-2)+1)) := by norm_num
end IndependentRecoveryCritic
