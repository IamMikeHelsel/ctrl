import HodgeBridge
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
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
  simp only [complement, Set.powersetCard.coe_compl, Finset.disjUnion_eq_union]
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
  simp only [complement, Set.powersetCard.coe_compl, Finset.disjUnion_eq_union]
  simp only [Finset.union_compl]
  rw [Fin.sort_univ]
  exact List.idxOf_finRange _

def I01 : Ix 2 := ⟨{0,1}, by change ({0,1} : Finset (Fin 14)).card=2; decide⟩
def I07 : Ix 2 := ⟨{0,7}, by change ({0,7} : Finset (Fin 14)).card=2; decide⟩

theorem order_I01 (i:Fin 2) : (I01).val.orderEmbOfFin (I01).property i =
    (![0,1] : Fin 2→Fin 14) i := by
  have he : (I01).val = ([0,1] : List (Fin 14)).toFinset := by
    ext a
    fin_cases a <;> simp [I01]
  have hs : (I01).val.sort = ([0,1] : List (Fin 14)) := by
    rw [he]
    exact (List.toFinset_sort (fun a b : Fin 14 => a ≤ b) (by decide)).mpr (by decide)
  simp only [Finset.orderEmbOfFin_apply, hs]
  fin_cases i <;> rfl

theorem order_comp_I01 (i:Fin 12) : (complement (by decide : 2+12=14) I01).val.orderEmbOfFin (complement (by decide : 2+12=14) I01).property i =
    (![2,3,4,5,6,7,8,9,10,11,12,13] : Fin 12→Fin 14) i := by
  have he : (complement (by decide : 2+12=14) I01).val = ([2,3,4,5,6,7,8,9,10,11,12,13] : List (Fin 14)).toFinset := by
    ext a
    fin_cases a <;> simp [I01, complement]
  have hs : (complement (by decide : 2+12=14) I01).val.sort = ([2,3,4,5,6,7,8,9,10,11,12,13] : List (Fin 14)) := by
    rw [he]
    exact (List.toFinset_sort (fun a b : Fin 14 => a ≤ b) (by decide)).mpr (by decide)
  simp only [Finset.orderEmbOfFin_apply, hs]
  fin_cases i <;> rfl

theorem order_I07 (i:Fin 2) : (I07).val.orderEmbOfFin (I07).property i =
    (![0,7] : Fin 2→Fin 14) i := by
  have he : (I07).val = ([0,7] : List (Fin 14)).toFinset := by
    ext a
    fin_cases a <;> simp [I07]
  have hs : (I07).val.sort = ([0,7] : List (Fin 14)) := by
    rw [he]
    exact (List.toFinset_sort (fun a b : Fin 14 => a ≤ b) (by decide)).mpr (by decide)
  simp only [Finset.orderEmbOfFin_apply, hs]
  fin_cases i <;> rfl

theorem order_comp_I07 (i:Fin 12) : (complement (by decide : 2+12=14) I07).val.orderEmbOfFin (complement (by decide : 2+12=14) I07).property i =
    (![1,2,3,4,5,6,8,9,10,11,12,13] : Fin 12→Fin 14) i := by
  have he : (complement (by decide : 2+12=14) I07).val = ([1,2,3,4,5,6,8,9,10,11,12,13] : List (Fin 14)).toFinset := by
    ext a
    fin_cases a <;> simp [I07, complement]
  have hs : (complement (by decide : 2+12=14) I07).val.sort = ([1,2,3,4,5,6,8,9,10,11,12,13] : List (Fin 14)) := by
    rw [he]
    exact (List.toFinset_sort (fun a b : Fin 14 => a ≤ b) (by decide)).mpr (by decide)
  simp only [Finset.orderEmbOfFin_apply, hs]
  fin_cases i <;> rfl


def p07 : Equiv.Perm (Fin 14) :=
  Equiv.ofBijective (![0,7,1,2,3,4,5,6,8,9,10,11,12,13] : Fin 14 → Fin 14) (by decide)

theorem perm_I01 : Set.powersetCard.permOfDisjoint
    (s := I01) (t := complement (by decide : 2+12=14) I01)
    (by exact disjoint_compl_right) = Equiv.refl (Fin 14) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [perm_compl_left, order_I01]
    fin_cases j <;> rfl
  · intro j
    rw [perm_compl_right, order_comp_I01]
    fin_cases j <;> rfl

theorem perm_I07 : Set.powersetCard.permOfDisjoint
    (s := I07) (t := complement (by decide : 2+12=14) I07)
    (by exact disjoint_compl_right) = p07 := by
  apply Equiv.ext
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [perm_compl_left, order_I07]
    fin_cases j <;> rfl
  · intro j
    rw [perm_compl_right, order_comp_I07]
    fin_cases j <;> rfl

theorem eps_I01 : eps I01 = 1 := by
  unfold eps
  rw [Set.powersetCard.sign_eq_permOfDisjoint_sign (by decide : 2+12=Fintype.card (Fin 14))
    I01 (complement (by decide : 2+12=14) I01) (by exact disjoint_compl_right)]
  rw [perm_I01, Equiv.Perm.sign_refl]
  norm_num

theorem eps_I07 : eps I07 = 1 := by
  unfold eps
  rw [Set.powersetCard.sign_eq_permOfDisjoint_sign (by decide : 2+12=Fintype.card (Fin 14))
    I07 (complement (by decide : 2+12=14) I07) (by exact disjoint_compl_right)]
  rw [perm_I07]
  have hp : p07.sign = 1 := by
    rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
    decide
  rw [hp]
  norm_num

theorem mu_I01 : mu I01 = 1 := by norm_num [mu, I01, d]
theorem mu_I07 : mu I07 = -1 := by norm_num [mu, I07, d]


theorem S_I01 : S (by decide : 2+12=14) (e 2 I01) =
    e 12 (complement (by decide : 2+12=14) I01) := by
  rw [S_basis, eps_I01, mu_I01, mul_one, one_smul]

theorem H_I01 : H (by decide : 2+12=14) (e 2 I01) =
    -e 12 (complement (by decide : 2+12=14) I01) := by
  rw [H_basis, mu_complement, eps_I01, mu_I01, one_mul]
  exact neg_one_smul ℝ (e 12 (complement (by decide : 2+12=14) I01))

theorem S_I07 : S (by decide : 2+12=14) (e 2 I07) =
    -e 12 (complement (by decide : 2+12=14) I07) := by
  rw [S_basis, eps_I07, mu_I07, one_mul]
  exact neg_one_smul ℝ (e 12 (complement (by decide : 2+12=14) I07))

theorem H_I07 : H (by decide : 2+12=14) (e 2 I07) =
    e 12 (complement (by decide : 2+12=14) I07) := by
  rw [H_basis, mu_complement, eps_I07, mu_I07, neg_neg, one_mul, one_smul]

theorem star2_I01 : star2
    (subsetIndexEquiv 12 (complement (by decide : 2+12=14) I01))
    (subsetIndexEquiv 2 I01) = -1 := by
  rw [star2_signed_complement]
  simp only [Equiv.symm_apply_apply, ite_true, mu_complement, mu_I01, eps_I01, one_mul]

theorem star2_I07 : star2
    (subsetIndexEquiv 12 (complement (by decide : 2+12=14) I07))
    (subsetIndexEquiv 2 I07) = 1 := by
  rw [star2_signed_complement]
  simp only [Equiv.symm_apply_apply, ite_true, mu_complement, mu_I07, eps_I07, one_mul, neg_neg]

theorem I01_form_nonzero : e 2 I01 ≠ 0 := (e 2).ne_zero I01

theorem H_square_not_positive_I01 :
    H (by decide : 12+2=14) (H (by decide : 2+12=14) (e 2 I01)) ≠ e 2 I01 := by
  intro hh
  rw [H_square] at hh
  have hc := congrArg (fun x : E 2 => (e 2).repr x I01) hh
  norm_num only [map_neg, Finsupp.neg_apply, Basis.repr_self, Finsupp.single_eq_same] at hc

end GUHodgeBridge
