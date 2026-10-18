import Spec
import Init.Data.List.Lemmas

namespace Submission

def encodeRow (width : Nat) (row : List Nat) : List (Nat × Nat) :=
  (List.range width).filterMap fun j =>
    if row.getD j 0 = 0 then none else some (j, row.getD j 0)

def sparseRows : List (List (Nat × Nat)) → Nat → Nat
  | [], _ => 1
  | row :: rows, used =>
      row.foldl (fun total (j, entry) =>
        if used.testBit j then total
        else total + entry * sparseRows rows (used ||| (1 <<< j))) 0

theorem sparseRows_correct (width : Nat) (rows : List (List Nat)) (used : Nat) :
    sparseRows (rows.map (encodeRow width)) used = permanentRows width rows used := by
  induction rows generalizing used with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, sparseRows, encodeRow, List.foldl_filterMap, permanentRows]
    congr 1
    funext total j
    by_cases he : (row[j]?).getD 0 = 0
    · simp [he]
    · simp [he, ih]

def impl (n : Nat) : Nat :=
  let m := genPermanentMatrix (permanentDimension n) (permanentSeed n)
  sparseRows (m.map (encodeRow m.length)) 0

theorem impl_correct : ∀ n, impl n = permanentSpecN n := by
  intro n
  exact sparseRows_correct _ _ _

end Submission
