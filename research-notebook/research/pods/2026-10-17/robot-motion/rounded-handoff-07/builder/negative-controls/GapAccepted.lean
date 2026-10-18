import NativeCoverage
open NativeRational
def first : Piece := ⟨0,1,0,0,0,0⟩
def second : Piece := ⟨2,3,0,0,0,0⟩
example : check 3 [first,second] = true := by
  norm_num [check,chainOK,JoinOK,first,second]
