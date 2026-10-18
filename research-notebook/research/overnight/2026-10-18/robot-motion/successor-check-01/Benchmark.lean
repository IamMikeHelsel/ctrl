import SuccessorGuard

open RobotMotion RobotMotion.AccelerationAdmission.SuccessorCheck

def main (args : List String) : IO Unit := do
  let some raw := args.head? | throw (IO.userError "expected event count")
  let some n := raw.toNat? | throw (IO.userError "expected natural number")
  let es : List QEvent := (List.range n).map fun i =>
    ((i : Rat) / 100, if i % 2 = 0 then (1 : Rat) / 1000 else -(1 : Rat) / 1000)
  let started ← IO.monoNanosNow
  let accepted := checkSuccessor (1/5) (1/2) 0 es
  -- Printing forces the result before the final clock read. The interval
  -- includes this one-line output, but excludes Lean startup and elaboration.
  IO.println s!"accepted={accepted}"
  let finished ← IO.monoNanosNow
  IO.println s!"nanoseconds={finished-started}"
