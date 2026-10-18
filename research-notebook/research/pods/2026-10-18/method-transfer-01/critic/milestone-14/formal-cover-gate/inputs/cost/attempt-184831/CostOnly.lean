import Std
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace CostOnly
abbrev IV := Rat × Rat
def k (x : Rat) : IV := (x, x)
def add (a b : IV) : IV := (a.1+b.1, a.2+b.2)
def neg (a : IV) : IV := (-a.2, -a.1)
def sub (a b : IV) : IV := add a (neg b)
def mul (a b : IV) : IV :=
  (min (min (a.1*b.1) (a.1*b.2)) (min (a.2*b.1) (a.2*b.2)),
   max (max (a.1*b.1) (a.1*b.2)) (max (a.2*b.1) (a.2*b.2)))
def div (a b : IV) : IV := mul a (1/b.2, 1/b.1)
def sq (a : IV) : IV :=
  (if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0 else min (a.1*a.1) (a.2*a.2),
   max (a.1*a.1) (a.2*a.2))
def R : Rat := 251/10000
def bounds (c j : IV) (t : Rat) : IV × IV :=
  let y := div (k 1) (mul (k 2) c)
  let m := mul (mul (k 4) c) j
  let b := sub y (k (1/2))
  let L0 := sub (mul (k (8*R)) (sub y m)) (mul (k 2) m)
  let C := sub (sub j (mul (k (4*R)) (sq (sub y m)))) (sq m)
  let a := div (sub j (k R)) b
  let L1 := sub a (mul (k 2) m)
  let D2 := sq (sub L1 L0)
  let Hmin := sub (mul a m) (sq m)
  (add C (div (mul (k (t*t)) D2) (k (4*(4*R+1)))),
   add Hmin (div (mul (k ((1-t)*(1-t))) D2) (k 4)))
def ok (c j : IV) (t : Rat) : Bool :=
  let v := bounds c j t
  decide (0 < c.1 ∧ c.2 < 1 ∧ c.1 ≤ c.2 ∧ j.1 ≤ j.2 ∧
    (t = 0 ∨ t = 1) ∧ v.1.2 ≤ 0 ∧ v.2.2 ≤ 0)
theorem leaf_100 : ok ((12569 / 16000 : Rat), (50309 / 64000 : Rat)) ((63 / 1504 : Rat), (127 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_100
theorem leaf_103 : ok ((50309 / 64000 : Rat), (25171 / 32000 : Rat)) ((63 / 1504 : Rat), (127 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_103
theorem leaf_104 : ok ((50309 / 64000 : Rat), (25171 / 32000 : Rat)) ((127 / 3008 : Rat), (2 / 47 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_104
theorem leaf_130 : ok ((6301 / 8000 : Rat), (50441 / 64000 : Rat)) ((63 / 1504 : Rat), (127 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_130
theorem leaf_133 : ok ((50441 / 64000 : Rat), (25237 / 32000 : Rat)) ((63 / 1504 : Rat), (127 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_133
theorem leaf_139 : ok ((25237 / 32000 : Rat), (50507 / 64000 : Rat)) ((63 / 1504 : Rat), (127 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_139
theorem leaf_142 : ok ((50507 / 64000 : Rat), (2527 / 3200 : Rat)) ((63 / 1504 : Rat), (127 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_142
theorem leaf_166 : ok ((50573 / 64000 : Rat), (25303 / 32000 : Rat)) ((63 / 1504 : Rat), (127 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_166
theorem leaf_229 : ok ((50903 / 64000 : Rat), (6367 / 8000 : Rat)) ((61 / 1504 : Rat), (31 / 752 : Rat)) (1 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_229
theorem leaf_268 : ok ((6367 / 8000 : Rat), (50969 / 64000 : Rat)) ((61 / 1504 : Rat), (123 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_268
theorem leaf_271 : ok ((50969 / 64000 : Rat), (25501 / 32000 : Rat)) ((61 / 1504 : Rat), (123 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_271
theorem leaf_272 : ok ((50969 / 64000 : Rat), (25501 / 32000 : Rat)) ((123 / 3008 : Rat), (31 / 752 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_272
theorem leaf_299 : ok ((12767 / 16000 : Rat), (51101 / 64000 : Rat)) ((61 / 1504 : Rat), (123 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_299
theorem leaf_302 : ok ((51101 / 64000 : Rat), (25567 / 32000 : Rat)) ((61 / 1504 : Rat), (123 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_302
theorem leaf_303 : ok ((51101 / 64000 : Rat), (25567 / 32000 : Rat)) ((123 / 3008 : Rat), (31 / 752 : Rat)) (1 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_303
theorem leaf_311 : ok ((51167 / 64000 : Rat), (4 / 5 : Rat)) ((61 / 1504 : Rat), (123 / 3008 : Rat)) (0 / 1 : Rat) = true := by decide +kernel
#print axioms leaf_311
end CostOnly
