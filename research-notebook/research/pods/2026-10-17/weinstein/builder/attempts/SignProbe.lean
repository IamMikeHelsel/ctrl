import HodgeBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower
namespace GUHodgeBridge

theorem perm_value_left (I : Ix 2) (J : Ix 12) (h : Disjoint I.val J.val) (i : Fin 2) :
    ((Set.powersetCard.permOfDisjoint h) (Fin.castAdd 12 i)).val =
      (I.val.disjUnion J.val h).sort.idxOf (I.val.orderEmbOfFin I.property i) := by
  dsimp only [Set.powersetCard.permOfDisjoint, Equiv.trans_apply]
  rw [finSumFinEquiv_symm_apply_castAdd]
  simp [Set.powersetCard.orderIsoOfFin, Finset.orderIsoOfFin_symm_apply,
    Set.powersetCard.disjUnion]

theorem perm_value_right (I : Ix 2) (J : Ix 12) (h : Disjoint I.val J.val) (i : Fin 12) :
    ((Set.powersetCard.permOfDisjoint h) (Fin.natAdd 2 i)).val =
      (I.val.disjUnion J.val h).sort.idxOf (J.val.orderEmbOfFin J.property i) := by
  dsimp only [Set.powersetCard.permOfDisjoint, Equiv.trans_apply]
  rw [finSumFinEquiv_symm_apply_natAdd]
  simp [Set.powersetCard.orderIsoOfFin, Finset.orderIsoOfFin_symm_apply,
    Set.powersetCard.disjUnion]

theorem perm_compl_left (I : Ix 2) (i : Fin 2) :
    (Set.powersetCard.permOfDisjoint (s:=I) (t:=complement (by decide : 2+12=14) I)
      (by exact disjoint_compl_right)) (Fin.castAdd 12 i) = I.val.orderEmbOfFin I.property i := by
  apply Fin.ext
  rw [perm_value_left]
  simp only [complement, Set.powersetCard.coe_compl, Finset.disjUnion_eq_union,
    sup_compl_eq_top, Finset.top_eq_univ, Fin.sort_univ]
  simp only [Finset.union_compl]
  rw [Fin.sort_univ]
  exact List.idxOf_finRange _

theorem perm_compl_right (I : Ix 2) (i : Fin 12) :
    (Set.powersetCard.permOfDisjoint (s:=I) (t:=complement (by decide : 2+12=14) I)
      (by exact disjoint_compl_right)) (Fin.natAdd 2 i) =
      (complement (by decide : 2+12=14) I).val.orderEmbOfFin
        (complement (by decide : 2+12=14) I).property i := by
  apply Fin.ext
  rw [perm_value_right]
  simp only [complement, Set.powersetCard.coe_compl, Finset.disjUnion_eq_union,
    sup_compl_eq_top, Finset.top_eq_univ, Fin.sort_univ]
  simp only [Finset.union_compl]
  rw [Fin.sort_univ]
  exact List.idxOf_finRange _
end GUHodgeBridge
