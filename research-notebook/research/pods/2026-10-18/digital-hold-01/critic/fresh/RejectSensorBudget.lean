import DigitalHold
open LeanControls.DigitalHold
example : |command 0 (![-1/1000,-1/100,-1/20]) - command 0 (![0,0,0])| ≤ 92/1000 := by
  norm_num [command]
