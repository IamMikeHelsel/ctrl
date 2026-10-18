import FiniteGraphBridge
import UniversalSelector
import BCLTransport
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
namespace Erdos128.FinalGraph
open scoped BigOperators
open FiniteProfileBridge CompletionBridge
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def smallEdges (C : OrientedBCLCut G) : ℚ :=
 (edgeCountOn G C.small : ℚ)/(Fintype.card V : ℚ)^2

theorem actual_cut_budget [Nonempty V] (C : OrientedBCLCut G) :
 0 ≤ smallEdges C ∧ 0 ≤ sideEdges C ∧ smallEdges C+sideEdges C ≤ E10.I := by
 have hn : 0 < (Fintype.card V : ℚ)^2 := sq_pos_of_pos (by exact_mod_cast Fintype.card_pos)
 have hb : (edgeCountOn G C.small : ℚ)+(edgeCountOn G C.large : ℚ) ≤
   E10.I*(Fintype.card V : ℚ)^2 := by
  simpa only [Nat.cast_add,OrientedBCLCut.large,E10.I] using C.internal_bound
 refine ⟨div_nonneg (Nat.cast_nonneg _) hn.le,div_nonneg (Nat.cast_nonneg _) hn.le,?_⟩
 unfold smallEdges sideEdges
 rw [← add_div]
 exact (div_le_iff₀ hn).2 hb

theorem inverse_side [Nonempty V] (C : OrientedBCLCut G) :
 sideMass C = 1/(2*C.c) := by
 have hn : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
 have hk : (C.large.card : ℚ) ≠ 0 := by exact_mod_cast C.large_nonempty.card_ne_zero
 unfold sideMass OrientedBCLCut.c
 field_simp [hn,hk]

theorem small_ratio [Nonempty V] (C : OrientedBCLCut G) :
 (C.small.card : ℚ)/(Fintype.card V : ℚ) = E10.xval C.c := by
 have hn : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
 have hs : (C.small.card : ℚ)+(C.large.card : ℚ) = (Fintype.card V : ℚ) := by
  exact_mod_cast C.small_card_add_large_card
 rw [E10.xval,←inverse_side C]
 unfold sideMass
 apply (div_eq_iff hn).2
 field_simp [hn]
 nlinarith

theorem completion_agrees (c : ℚ) :
 completionEnvelope (E10.xval c) (1/2) = E10.completion c := by
 have hb : 4*E10.xval c ≤ 3*(1/2:ℚ) ↔ E10.xval c ≤ 3/8 := by constructor <;> intro h <;> linarith
 unfold completionEnvelope E10.completion E10.Q
 simp only [hb]
 split_ifs <;> ring

theorem actual_completion_scale [Nonempty V] (C : OrientedBCLCut G) (t : ℕ)
 (hhalf : 2*t=Fintype.card V) :
 completionEnvelope C.small.card t = (Fintype.card V : ℚ)^2 * E10.completion C.c := by
 have hn : (0:ℚ)<Fintype.card V := by exact_mod_cast Fintype.card_pos
 have ht : (Fintype.card V : ℚ)*(1/2)=(t:ℚ) := by
  have hh : (2:ℚ)*t=Fintype.card V := by exact_mod_cast hhalf
  linarith
 have hs := completionEnvelope_scale (Fintype.card V : ℚ)
   ((C.small.card : ℚ)/(Fintype.card V : ℚ)) (1/2) hn
 rw [mul_div_cancel₀ _ hn.ne',ht,small_ratio C,completion_agrees] at hs
 exact hs

theorem fractional_of_oriented_cut_even [Nonempty V]
 (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
 (C : OrientedBCLCut G) (t : ℕ) (ht : 0<t) (hhalf : 2*t=Fintype.card V) :
 HasNormalizedFractionalHalfBoundQ G E10.R := by
 have hn : (0:ℚ)<Fintype.card V := by exact_mod_cast Fintype.card_pos
 have hn2 := sq_pos_of_pos hn
 have hy : (0:ℚ)<C.large.card := by exact_mod_cast C.large_nonempty.card_pos
 have hsum := C.small_card_add_large_card
 have hord : C.small.card ≤ C.large.card := C.card_le_compl
 have hXt : C.small.card ≤ t := by omega
 have htY : t ≤ C.large.card := by omega
 have hc : C.c=(t:ℚ)/(C.large.card:ℚ) := by
  unfold OrientedBCLCut.c
  have hh : (Fintype.card V:ℚ)=2*(t:ℚ) := by exact_mod_cast hhalf.symm
  rw [hh]
  ring
 have hb := actual_cut_budget C
 have hj : sideEdges C ≤ E10.I := by linarith [hb.1,hb.2.2]
 rcases E10.universal_selector C.c (sideEdges C) C.one_half_le_c C.c_le_one hb.2.1 hj with hU|hQ|hM
 · obtain ⟨z,hz,hcost⟩ := uniform_side_fractional_half G C.large C.large_nonempty t htY hhalf
   refine ⟨z,hz,?_⟩
   calc
    normalizedEdgeCostQ G z ≤ (((t:ℚ)/(C.large.card:ℚ))^2*(edgeCountOn G C.large:ℚ))/(Fintype.card V:ℚ)^2 :=
      div_le_div_of_nonneg_right hcost hn2.le
    _ = C.c^2*sideEdges C := by rw [hc];unfold sideEdges;ring
    _ ≤ E10.R := hU
 · have hthird : 2*t ≤ 3*C.small.card := by
    have hdiv : (3/4:ℚ)*(C.large.card:ℚ) ≤ (t:ℚ) := (le_div_iff₀ hy).1 (by simpa only [hc] using hQ.1)
    have hs : (C.small.card:ℚ)+(C.large.card:ℚ)=(Fintype.card V:ℚ) := by exact_mod_cast hsum
    have hh : (2:ℚ)*t=Fintype.card V := by exact_mod_cast hhalf
    have hr : (2:ℚ)*t≤3*(C.small.card:ℚ) := by linarith
    exact_mod_cast hr
   obtain ⟨z,hz,hcost⟩ := deletion_completion_even G htri C.small t hhalf hthird hXt
   refine ⟨z,hz,?_⟩
   calc
    normalizedEdgeCostQ G z ≤ (completionEnvelope C.small.card t+(edgeCountOn G C.small:ℚ))/(Fintype.card V:ℚ)^2 :=
      div_le_div_of_nonneg_right hcost hn2.le
    _ = E10.completion C.c+smallEdges C := by
      rw [actual_completion_scale C t hhalf]
      unfold smallEdges
      field_simp [hn.ne']
    _ ≤ E10.completion C.c+E10.I-sideEdges C := by linarith [hb.2.2]
    _ ≤ E10.R := hQ.2
 · obtain ⟨hc1,L,hA,hH⟩ := hM
   have hym : 1/2<sideMass C := by
    rw [inverse_side C]
    exact (lt_div_iff₀ (mul_pos (by norm_num) C.c_pos)).2 (by linarith)
   rw [←inverse_side C] at hA hH
   exact half_from_squared_certificates C htri E10.R L hym (by norm_num [E10.R]) hA hH

/-- Arbitrary finite order, conditional on exactly the transparent eventual BCL input. -/
theorem fractional_251_10000_all_orders
 (hBCL : BCLEventual.{u}) (G : SimpleGraph V) [DecidableRel G.Adj]
 (htri : G.CliqueFree 3) : HasNormalizedFractionalHalfBoundQ G (251/10000:ℚ) := by
 classical
 cases isEmpty_or_nonempty V with
 | inl hempty =>
   letI : IsEmpty V := hempty
   refine ⟨fun _ => 0,⟨by intro v;exact isEmptyElim v,by simp⟩,?_⟩
   norm_num [normalizedEdgeCostQ,edgeCost,edgeBilin]
 | inr hne =>
   letI : Nonempty V := hne
   let H := balancedBlowup G 2
   have hHtri : H.CliqueFree 3 := cliqueFree_balancedBlowup G 2 (by omega) htri
   have hcut : BCLCutCertificate H := bclCutCertificate_all_of_eventually hBCL (V × Fin 2) H hHtri
   obtain ⟨C⟩ := exists_orientedBCLCut H hcut
   have hh : 2*Fintype.card V=Fintype.card (V × Fin 2) := by simp [Fintype.card_prod,Nat.mul_comm]
   have hnorm := fractional_of_oriented_cut_even H hHtri C (Fintype.card V) Fintype.card_pos hh
   exact (hasNormalizedFractionalHalfBoundQ_balancedBlowup_iff G 2 (by omega) _).1 hnorm

/-- The all-finite-graph floor-half endpoint. BCLEventual is the only external mathematical hypothesis. -/
theorem sparse_half_251_10000
 (hBCL : BCLEventual.{u}) (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3) :
 ∃ S : Finset V, S.card=Fintype.card V/2 ∧
 (edgeCountOn G S:ℚ)≤(251/10000:ℚ)*(Fintype.card V:ℚ)^2 := by
 classical
 change HasSparseHalf G _
 cases isEmpty_or_nonempty V with
 | inl hempty =>
   letI : IsEmpty V := hempty
   exact ⟨∅,by simp,by simp [edgeCountOn]⟩
 | inr hne =>
   letI : Nonempty V := hne
   obtain ⟨z,hz,hcost⟩ := fractional_251_10000_all_orders hBCL G htri
   apply hasSparseHalf_of_hasFractionalHalfBound G
   refine ⟨z,hz,?_⟩
   exact (div_le_iff₀ (sq_pos_of_pos (show (0:ℚ)<Fintype.card V by exact_mod_cast Fintype.card_pos))).1 hcost
end
end Erdos128.FinalGraph
