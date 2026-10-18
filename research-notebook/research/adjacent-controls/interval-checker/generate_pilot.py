from fractions import Fraction as F
from pathlib import Path
import json, math
p=Path(__file__).resolve().parent
row=json.loads((p/'coefficient-data.json').read_text())[0]
E,B,C=[tuple(map(F,row[k])) for k in ['E','B','C']]
pt=lambda x:(F(x),F(x))
add=lambda a,b:(a[0]+b[0],a[1]+b[1])
neg=lambda a:(-a[1],-a[0])
sub=lambda a,b:add(a,neg(b))
def mul(a,b):
 v=[x*y for x in a for y in b];return min(v),max(v)
clip=lambda a:tuple(max(F(-1),min(F(1),v)) for v in a)
D=2**44
rnd=lambda a:(F(math.floor(a[0]*D),D),F(math.ceil(a[1]*D),D))
X=[[(F(99,100),F(199,200)),(F(49,100),F(99,200)),(F(-1,100),F(-1,200))]]
for n in range(25):
 x,v,a=X[-1];u=clip(neg(add(add(x,mul(pt(3),v)),mul(pt(2),a))))
 X.append(list(map(rnd,[add(add(add(x,mul(pt(F(1,20)),v)),mul(C,a)),mul(sub(pt(F(1,800)),C),u)),add(add(v,mul(B,a)),mul(sub(pt(F(1,20)),B),u)),add(mul(E,a),mul(sub(pt(1),E),u))])))
q=lambda x:f'({x.numerator}/{x.denominator}:ℚ)'
iv=lambda a:'⟨'+q(a[0])+','+q(a[1])+'⟩'
bx=lambda a:'!['+','.join(map(iv,a))+']'
s='''module
public import IntervalChecker
@[expose] public section
noncomputable section
namespace LeanControls.IntervalPilot
open IntervalChecker
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
'''
s+=f'def coeff : Coefficients := ⟨point (1/20), point (1/800), {iv(E)}, {iv(B)}, {iv(C)}⟩\n'
s+='def boxes : ℕ → Box\n'
for n,x in enumerate(X):s+=f'  | {n} => {bx(x)}\n'
s+=f'  | _ => {bx(X[-1])}\n'
s+='''theorem checked_steps : ∀ n<25, BoxSubset (sampledBox coeff (boxes n) (point 0) (point 0)) (boxes (n+1)) := by
  intro n hn
  interval_cases n <;> intro i <;> fin_cases i <;>
    norm_num [BoxSubset, IntervalChecker.Subset, sampledBox, heldBox, commandBox, coeff, boxes,
      IntervalChecker.add, IntervalChecker.sub, IntervalChecker.neg, IntervalChecker.mul,
      clip1, point]

theorem endpoints {r : ℝ} {z : UncertainLag.State} (hk : CoeffMem coeff r (1/20))
    (hz : BoxMem (boxes 0) z) :
    ∀ n≤25, BoxMem (boxes n) (stateTrace (fun _=>r) (fun _=>1/20)
      (fun _=>0) (fun _=>0) z n) := by
  exact certificate_trace_sound _ _ _ _ (fun _=>coeff) (fun _=>point 0) (fun _=>point 0)
    boxes hz (fun _ _=>hk) (fun _ _=>by simpa using point_mem 0) (fun _ _=>by simpa using point_mem 0) checked_steps
end LeanControls.IntervalPilot
#print axioms LeanControls.IntervalPilot.checked_steps
#print axioms LeanControls.IntervalPilot.endpoints
'''
(p/'IntervalPilot.lean').write_text(s)
(p/'pilot-data.json').write_text(json.dumps({'rate_cell':[row['lo'],row['hi']],'steps':25,'dt':'1/20','outward_grid_denominator':D,'errors':'zero','boxes':[[[str(y) for y in a] for a in x] for x in X],'scope':'Proposed rational certificate; Lean compilation decides acceptance. Coefficient bridge separately required.'},indent=2)+'\n')
print('Generated25steps; finalbox',[[float(y) for y in a] for a in X[-1]])
