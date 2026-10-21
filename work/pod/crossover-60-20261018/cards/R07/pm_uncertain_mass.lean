import Mathlib.Tactic
namespace R07Mass
/-- Same state, common action, exact task acceleration in both declared models.
This is not an impossibility theorem for all adaptive feedback policies. -/
theorem common_action_zero (t1 t2 : ℝ)
    (h1 : t1+t2/2=0) (h2 : t1+t2/(101/50)=0) : t1=0 ∧ t2=0 := by
  constructor <;> linarith

theorem unchanged_torque_drift :
    (-1/10:ℝ)+(1/5)/(101/50)= -1/1010 ∧
    ((-1/1010:ℝ)*2^2/2)= -1/505 ∧
    ((101/50:ℝ)/10)>1/5 := by norm_num

#print axioms common_action_zero
#print axioms unchanged_torque_drift
end R07Mass
