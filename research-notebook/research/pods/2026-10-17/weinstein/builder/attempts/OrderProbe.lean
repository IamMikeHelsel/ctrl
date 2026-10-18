import HodgeBridge
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
open Module exteriorPower
namespace GUHodgeBridge

def I01 : Ix 2 := ⟨{0,1}, by change ({0,1} : Finset (Fin 14)).card=2; decide⟩
def I07 : Ix 2 := ⟨{0,7}, by change ({0,7} : Finset (Fin 14)).card=2; decide⟩

theorem order_I01 (i:Fin 2) : (I01).val.orderEmbOfFin (I01).property i =
    (![0,1] : Fin 2→Fin 14) i := by
  have he : (I01).val = ([0,1] : List (Fin 14)).toFinset := by
    ext a
    fin_cases a <;> simp [I01, I07, complement]
  have hs : (I01).val.sort = ([0,1] : List (Fin 14)) := by
    rw [he]
    exact (List.toFinset_sort (fun a b : Fin 14 => a ≤ b) (by decide)).mpr (by decide)
  simp only [Finset.orderEmbOfFin_apply, hs]
  fin_cases i <;> rfl

theorem order_comp_I01 (i:Fin 12) : (complement (by decide : 2+12=14) I01).val.orderEmbOfFin (complement (by decide : 2+12=14) I01).property i =
    (![2,3,4,5,6,7,8,9,10,11,12,13] : Fin 12→Fin 14) i := by
  have he : (complement (by decide : 2+12=14) I01).val = ([2,3,4,5,6,7,8,9,10,11,12,13] : List (Fin 14)).toFinset := by
    ext a
    fin_cases a <;> simp [I01, I07, complement]
  have hs : (complement (by decide : 2+12=14) I01).val.sort = ([2,3,4,5,6,7,8,9,10,11,12,13] : List (Fin 14)) := by
    rw [he]
    exact (List.toFinset_sort (fun a b : Fin 14 => a ≤ b) (by decide)).mpr (by decide)
  simp only [Finset.orderEmbOfFin_apply, hs]
  fin_cases i <;> rfl

theorem order_I07 (i:Fin 2) : (I07).val.orderEmbOfFin (I07).property i =
    (![0,7] : Fin 2→Fin 14) i := by
  have he : (I07).val = ([0,7] : List (Fin 14)).toFinset := by
    ext a
    fin_cases a <;> simp [I01, I07, complement]
  have hs : (I07).val.sort = ([0,7] : List (Fin 14)) := by
    rw [he]
    exact (List.toFinset_sort (fun a b : Fin 14 => a ≤ b) (by decide)).mpr (by decide)
  simp only [Finset.orderEmbOfFin_apply, hs]
  fin_cases i <;> rfl

theorem order_comp_I07 (i:Fin 12) : (complement (by decide : 2+12=14) I07).val.orderEmbOfFin (complement (by decide : 2+12=14) I07).property i =
    (![1,2,3,4,5,6,8,9,10,11,12,13] : Fin 12→Fin 14) i := by
  have he : (complement (by decide : 2+12=14) I07).val = ([1,2,3,4,5,6,8,9,10,11,12,13] : List (Fin 14)).toFinset := by
    ext a
    fin_cases a <;> simp [I01, I07, complement]
  have hs : (complement (by decide : 2+12=14) I07).val.sort = ([1,2,3,4,5,6,8,9,10,11,12,13] : List (Fin 14)) := by
    rw [he]
    exact (List.toFinset_sort (fun a b : Fin 14 => a ≤ b) (by decide)).mpr (by decide)
  simp only [Finset.orderEmbOfFin_apply, hs]
  fin_cases i <;> rfl

end GUHodgeBridge
