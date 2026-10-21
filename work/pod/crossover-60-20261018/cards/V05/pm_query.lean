import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
noncomputable section
namespace V05Query
abbrev V := EuclideanSpace ℝ (Fin 3)
def prediction (i : Fin 4) : V :=
  WithLp.toLp 2 (![![-1,-1,-1],![-1,1,1],![1,-1,1],![5/3,5/3,-5/3]] i)
lemma prediction_separation (i j : Fin 4) (hij : i≠j) :
    8 ≤ dist (prediction i) (prediction j)^2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | norm_num [prediction, Fin.sum_univ_succ, PiLp.sub_apply]
/-- Four declared predictions have disjoint radius-one measurement balls.
Candidate completeness and prediction-to-pose binding are separate premises. -/
theorem no_shared_readout (i j : Fin 4) (hij : i≠j) (y : V) :
    ¬(dist (prediction i) y≤1 ∧ dist (prediction j) y≤1) := by
  intro h
  have ht := dist_triangle (prediction i) y (prediction j)
  rw [dist_comm y (prediction j)] at ht
  have hn := dist_nonneg (x:=prediction i) (y:=prediction j)
  have hs := prediction_separation i j hij
  have hu : dist (prediction i) (prediction j)≤2 := by linarith [h.1,h.2]
  nlinarith
#print axioms prediction_separation
#print axioms no_shared_readout
end V05Query
