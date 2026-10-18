import FinalGraph
import FiniteControls
set_option maxHeartbeats 5000000
set_option maxRecDepth 5000
namespace Erdos128.FinalControls
open scoped BigOperators
open FinalGraph FiniteProfileBridge CompletionBridge

def cycle5 : SimpleGraph (Fin 5) where
 Adj u v := (u.val+1)%5=v.val ∨ (v.val+1)%5=u.val
 symm := ⟨by intro u v h;exact h.symm⟩
 loopless := ⟨by intro v;fin_cases v <;> decide⟩
instance : DecidableRel cycle5.Adj := fun u v =>
 inferInstanceAs (Decidable ((u.val+1)%5=v.val ∨ (v.val+1)%5=u.val))

theorem cycle5_triangle_free : cycle5.CliqueFree 3 := by
 have hh : ∀ u v w : Fin 5, cycle5.Adj u v → cycle5.Adj u w → cycle5.Adj v w → False := by decide +kernel
 intro s hs
 obtain ⟨u,v,w,huv,huw,hvw,_⟩ := SimpleGraph.is3Clique_iff.mp hs
 exact hh u v w huv huw hvw

def oddCut : OrientedBCLCut cycle5 where
 small := {0,2}
 card_le_compl := by decide
 internal_bound := by decide +kernel

theorem odd_parameters : oddCut.c=5/6 ∧ sideEdges oddCut=1/25 ∧ smallEdges oddCut=0 := by
 decide +kernel

def doubled : SimpleGraph (Fin 5 × Fin 2) := balancedBlowup cycle5 2
instance : DecidableRel doubled.Adj := fun u v =>
 inferInstanceAs (Decidable (cycle5.Adj u.1 v.1))
def doubleCut : OrientedBCLCut doubled where
 small := Finset.univ.filter (fun p => p.1=0 ∨ p.1=2)
 card_le_compl := by decide
 internal_bound := by decide +kernel

theorem double_parameters : doubleCut.small.card=4 ∧ doubleCut.c=5/6 ∧
 sideEdges doubleCut=1/25 ∧ smallEdges doubleCut=0 := by decide +kernel

theorem odd_uses_completion : E10.R < oddCut.c^2*sideEdges oddCut ∧
 E10.completion oddCut.c+E10.I-sideEdges oddCut < E10.R := by decide +kernel

theorem doubled_completion_cost : completionEnvelope (4:ℚ) 5=2 ∧
 (10:ℚ)^2*E10.completion (5/6)=2 := by decide +kernel

noncomputable section

theorem explicit_even_cut_endpoint : HasNormalizedFractionalHalfBoundQ
 FiniteProfileControls.oneEdge E10.R :=
 fractional_of_oriented_cut_even FiniteProfileControls.oneEdge
  FiniteProfileControls.oneEdge_triangle_free FiniteProfileControls.cut 3 (by decide) (by decide)

theorem explicit_odd_cut_endpoint : HasNormalizedFractionalHalfBoundQ cycle5 E10.R := by
 have htri : doubled.CliqueFree 3 := cliqueFree_balancedBlowup cycle5 2 (by decide) cycle5_triangle_free
 have hh := fractional_of_oriented_cut_even doubled htri doubleCut 5 (by decide) (by decide)
 exact (hasNormalizedFractionalHalfBoundQ_balancedBlowup_iff cycle5 2 (by decide) E10.R).1 hh

theorem odd_floor_endpoint : ∃ S : Finset (Fin 5), S.card=2 ∧ (edgeCountOn cycle5 S:ℚ)≤251/400 := by
 obtain ⟨z,hz,hcost⟩ := explicit_odd_cut_endpoint
 have hr : HasFractionalHalfBound cycle5 (251/400) := by
  refine ⟨z,hz,?_⟩
  norm_num [normalizedEdgeCostQ,E10.R] at hcost
  linarith
 have hs := hasSparseHalf_of_hasFractionalHalfBound cycle5 hr
 simpa only [HasSparseHalf,Fintype.card_fin] using hs

theorem odd_explicit_floor : ({0,2}:Finset (Fin 5)).card=2 ∧ edgeCountOn cycle5 {0,2}=0 := by decide +kernel

theorem odd_three_have_edge : ∀ S : Finset (Fin 5), S.card=3 → 1≤edgeCountOn cycle5 S := by decide +kernel

theorem odd_ceil_impossible : ¬ ∃ S : Finset (Fin 5), S.card=3 ∧ (edgeCountOn cycle5 S:ℚ)≤E10.R*25 := by
 rintro ⟨S,hS,hcost⟩
 have he : (1:ℚ)≤edgeCountOn cycle5 S := by exact_mod_cast odd_three_have_edge S hS
 norm_num [E10.R] at hcost
 linarith

def k2 : SimpleGraph (Fin 2) where
 Adj u v := u≠v
 symm := ⟨by intro u v h;exact h.symm⟩
 loopless := ⟨by intro v h;exact h rfl⟩
instance : DecidableRel k2.Adj := fun u v => inferInstanceAs (Decidable (u≠v))
def balancedCut : OrientedBCLCut k2 where
 small := {0}
 card_le_compl := by decide
 internal_bound := by decide +kernel

theorem k2_triangle_free : k2.CliqueFree 3 := by
 have hh : ∀ u v w : Fin 2, k2.Adj u v → k2.Adj u w → k2.Adj v w → False := by decide +kernel
 intro s hs
 obtain ⟨u,v,w,huv,huw,hvw,_⟩ := SimpleGraph.is3Clique_iff.mp hs
 exact hh u v w huv huw hvw

theorem balanced_parameters : balancedCut.c=1 ∧ sideMass balancedCut=1/2 ∧
 sideEdges balancedCut=0 ∧ ¬balancedCut.c<1 := by decide +kernel

theorem balanced_actual_endpoint : HasNormalizedFractionalHalfBoundQ k2 E10.R :=
 fractional_of_oriented_cut_even k2 k2_triangle_free balancedCut 1 (by decide) (by decide)

theorem even_nonzero_raw_cost :
 edgeCost FiniteProfileControls.oneEdge (FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ)))=9/25 := by
 have h := FiniteProfileControls.constant_half_and_cost.2
 norm_num [normalizedEdgeCostQ] at h
 linarith

theorem directed_edge_count_control :
 (∑ u : Fin 6, ∑ v : Fin 6, if FiniteProfileControls.oneEdge.Adj u v then
  FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ)) u *
  FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ)) v else 0)=18/25 := by
 have h := two_mul_edgeCost_eq_ordered_sum_low FiniteProfileControls.oneEdge
  (FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ)))
 rw [even_nonzero_raw_cost] at h
 linarith

theorem missing_order_square_control :
 edgeCost FiniteProfileControls.oneEdge (FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ))) ≠
 normalizedEdgeCostQ FiniteProfileControls.oneEdge (FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ))) := by
 rw [even_nonzero_raw_cost,FiniteProfileControls.constant_half_and_cost.2]
 norm_num

theorem empty_explicit_floor :
 (∅ : Finset (Fin 0)).card = Fintype.card (Fin 0)/2 ∧
 (edgeCountOn (⊥ : SimpleGraph (Fin 0)) ∅ : ℚ) ≤ E10.R*(Fintype.card (Fin 0):ℚ)^2 := by
 norm_num [edgeCountOn]

theorem branch_join_control : E10.completion (4/5)=3/128 ∧
 completionEnvelope (3:ℚ) 4=3/2 ∧ (8:ℚ)^2*E10.completion (4/5)=3/2 := by decide +kernel
end
end Erdos128.FinalControls
