#!/usr/bin/env python3
"""Untrusted coefficient generator. Lean checks every real inequality."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parent
N=16
D=10**12
EPS=F(1,10**18)
def rat(q):
 q=F(q);return f'(({q.numerator}/{q.denominator}:ℚ):ℝ)'
def coefficients(k):return [(-1)**m*F(1,20)**(m+k)/factorial(m+k)for m in range(10-k)]
def poly(k):return ' + '.join(f'{rat(c)}*r^{m}'for m,c in enumerate(coefficients(k)))
def bounds(lo,hi,k):
 cs=coefficients(k)
 lower=sum((c*(lo if c>=0 else hi)**m for m,c in enumerate(cs)),F(0))
 upper=sum((c*(hi if c>=0 else lo)**m for m,c in enumerate(cs)),F(0))
 err=EPS/lo**k
 return F(((lower-err)*D)//1-1,D),F(-((-(upper+err)*D)//1)+1,D)
out=['''module
public import CoefficientBounds
@[expose] public section
noncomputable section
namespace LeanControls.CoefficientCells
open CoefficientBounds
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
''']
for k,name in enumerate(['expPoly','velocityPoly','positionPoly']):
 out.append(f'''theorem {name}_expanded (r : ℝ) : {name} r = {poly(k)} := by
  norm_num [{name}, Finset.sum_range_succ, Nat.factorial]
  ring
''')
records=[]
for j in range(N):
 lo=F(9,10)+F(j,5*N);hi=F(9,10)+F(j+1,5*N)
 eb,bb,cb=[bounds(lo,hi,k)for k in range(3)]
 records.append({'lo':str(lo),'hi':str(hi),'E':list(map(str,eb)),'B':list(map(str,bb)),'C':list(map(str,cb))})
 terms=['Real.exp (-r/20)','(1-Real.exp (-r/20))/r','(1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2']
 goals=[f'{rat(a)} ≤ {t} ∧ {t} ≤ {rat(b)}' for (a,b),t in zip([eb,bb,cb],terms)]
 out.append(f'''theorem cell_{j} {{r : ℝ}} (hrlo : {rat(lo)} ≤ r) (hrhi : r ≤ {rat(hi)}) :
    ({goals[0]}) ∧ ({goals[1]}) ∧ ({goals[2]}) := by
  obtain ⟨δ, hd, he, hb, hc⟩ := shared_remainder (r := r) (by linarith) (by linarith)
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hirlo : {rat(1/hi)} ≤ r⁻¹ := by
    have hh := one_div_le_one_div_of_le (show 0 < r by linarith) hrhi
    norm_num at hh ⊢
    exact hh
  have hirhi : r⁻¹ ≤ {rat(1/lo)} := by
    have hh := one_div_le_one_div_of_le (show 0 < {rat(lo)} by norm_num) hrlo
    norm_num at hh ⊢
    exact hh
  have hb' : (1-Real.exp (-r/20))/r = velocityPoly r - δ*r⁻¹ :=
    hb.trans (by rw [div_eq_mul_inv])
  have hc' : (1/20:ℝ)/r-(1-Real.exp (-r/20))/r^2 = positionPoly r + δ*(r⁻¹)^2 :=
    hc.trans (by rw [div_eq_mul_inv, ← inv_pow])
  rw [hc', hb', he, expPoly_expanded, velocityPoly_expanded, positionPoly_expanded]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    dyadic_interval (native := false) [prec := 60]
''')
out.append('end LeanControls.CoefficientCells\n')
source='\n'.join(out)
if '--check'in sys.argv:
 assert (HERE/'CoefficientCells.lean').read_text()==source
 assert json.loads((HERE/'coefficient-data.json').read_text())==records
 print('Exact regeneration matches.')
else:
 (HERE/'CoefficientCells.lean').write_text(source)
 (HERE/'coefficient-data.json').write_text(json.dumps(records,indent=2)+'\n')
 print('Generated16 closed coefficient cells.')
