#!/usr/bin/env python3
"""Untrusted rational producer; all emitted assertions are checked by Lean."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
N = 32

def rat(x):
    x = F(x)
    return f'(({x.numerator}/{x.denominator}:ℚ):ℝ)'

def rounded_bounds(q):
    q = q / 2
    s = sum((q**m / factorial(m) for m in range(10)), F(0))
    err = abs(q)**10 * F(11, factorial(10)*10)
    a = F((s-err)*10**6 // 1, 10**6)
    b = F(-(-(s+err)*10**6 // 1), 10**6)
    lo = F(a*a*10**6 // 1, 10**6)
    hi = F(-(-b*b*10**6 // 1), 10**6)
    assert 0 < a < b and lo <= a*a and b*b <= hi
    return a,b,lo,hi

out = ['''module
public import TerminalBase
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
@[expose] public section
noncomputable section
namespace LeanControls.RecoveryTerminal
open Matrix BernsteinCertificate
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
''']
bounds = []
for j in range(N+1):
    q = -F(5,4)*(F(9,10)+F(j,5*N))
    a,b,lo,hi = rounded_bounds(q)
    bounds.append((lo,hi))
    out.append(f'''theorem exp_point_{j} : {rat(lo)} ≤ Real.exp {rat(q)} ∧
    Real.exp {rat(q)} ≤ {rat(hi)} := by
  apply exp_point (a := {rat(a)}) (b := {rat(b)})
  all_goals norm_num [expApprox, expError, Finset.sum_range_succ, Nat.factorial]
''')

out.append('''theorem held_terminal_coordinates {r : ℝ} (hr : 0 < r) (z : Fin 3 → ℝ) :
    UncertainLag.heldSegment r (5/4) z (-1) =
      ![z 0 + z 1*1.25 - 0.78125 + (z 2+1)*r⁻¹*(1.25-(1-Real.exp (-r*(5/4)))*r⁻¹),
        z 1-1.25+(z 2+1)*(1-Real.exp (-r*(5/4)))*r⁻¹,
        -1+(z 2+1)*Real.exp (-r*(5/4))] := by
  have hn := ne_of_gt hr
  ext i
  fin_cases i <;> dsimp [UncertainLag.heldSegment, UncertainLag.heldSolution] <;>
    field_simp <;> ring
''')

for j in range(N):
    lo,hi=F(9,10)+F(j,5*N),F(9,10)+F(j+1,5*N)
    el,eu=bounds[j+1][0],bounds[j][1]
    out.append(f'''theorem cell_{j} {{r : ℝ}} {{z : Fin 3 → ℝ}}
    (hrlo : {rat(lo)} ≤ r) (hrhi : r ≤ {rat(hi)})
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
  have helo : {rat(el)} ≤ Real.exp (-r*(5/4)) :=
    exp_point_{j+1}.1.trans (Real.exp_le_exp.mpr (by linarith))
  have hehi : Real.exp (-r*(5/4)) ≤ {rat(eu)} :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_point_{j}.2
  have hirlo : {rat(1/hi)} ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ {rat(1/lo)} := by
    have hh := one_div_le_one_div_of_le (show 0 < {rat(lo)} by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  rw [held_terminal_coordinates (by linarith), energy_ldl]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_fin_one]
  dsimp
  dyadic_interval (native := false) [prec := 30]
''')

out.append('''theorem terminal_energy {r : ℝ} {z : Fin 3 → ℝ}
    (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (hx : z 0 ∈ Set.Icc ((99/100:ℚ):ℝ) ((101/100:ℚ):ℝ))
    (hv : z 1 ∈ Set.Icc ((49/100:ℚ):ℝ) ((51/100:ℚ):ℝ))
    (ha : z 2 ∈ Set.Icc ((-1/100:ℚ):ℝ) ((1/100:ℚ):ℝ)) :
    energy Generated.TravelQuarterLower.P (UncertainLag.heldSegment r (5/4) z (-1)) ≤ 12 := by
''')
for j in range(N-1):
    hi = F(9,10)+F(j+1,5*N)
    out.append(f'  by_cases h{j} : r ≤ {rat(hi)}\n')
    out.append(f'  · exact cell_{j} (by linarith) h{j} hx hv ha\n')
out.append(f'  exact cell_{N-1} (by linarith) (by norm_num; exact hrhi) hx hv ha\n')
out.append('''#print axioms terminal_energy
end LeanControls.RecoveryTerminal
''')
generated = '\n'.join(out)
if '--check' in sys.argv:
    assert (ROOT/'TerminalCells.lean').read_text() == generated, 'Generated source differs'
    print('Regeneration matches checked TerminalCells.lean exactly.')
else:
    (ROOT/'TerminalCells.lean').write_text(generated)
    print(f'Wrote {N+1} exponential certificates, {N} closed interval certificates.')
