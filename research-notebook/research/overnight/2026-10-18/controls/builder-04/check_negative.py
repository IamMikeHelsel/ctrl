"""Exact numerical controls; no solver and no imports from builder search."""
from pathlib import Path
from fractions import Fraction as F
import itertools,json,hashlib
P=Path(__file__).resolve().parent
c=json.loads((P/'candidate.json').read_text());Q=[[F(x) for x in row] for row in c['Q']]
def det(A):
 if not A:return F(1)
 return sum((-1)**j*A[0][j]*det([r[:j]+r[j+1:] for r in A[1:]]) for j in range(len(A)))
def pd(A):return all(det([[A[i][j] for j in ids] for i in ids])>0 for k in range(1,len(A)+1) for ids in itertools.combinations(range(len(A)),k))
def energy(x,y,z):return (49597375*x*x+120006000*x*y+51027750*x*z+212058000*y*y+113732000*y*z+102314375*z*z)/F(68317631)
def rate(r,d,x,y,z):
 return ((2*49597375*x+120006000*y+51027750*z)*40*y+(120006000*x+2*212058000*y+113732000*z)*40*z+(51027750*x+113732000*y+2*102314375*z)*(-F(r,2)*x-F(3*r,2)*y-F(3*r,2)*z+F(r,2)*d))/68317631
bad=[row.copy() for row in Q];bad[2][2]=F(1,100)
checks={
 'original_Q_PD':pd(Q),
 'small_Q22_rejected':not pd(bad),
 'remove_input_bound_rejected':not (rate(80,2,2,0,0)<=20*(1-energy(2,0,0))),
 'remove_rate_upper_bound_rejected':not(rate(160,-1,-2,2,-1)<=20*(1-energy(-2,2,-1))),
 'reset_initial_energy_rejected':not(energy(16,0,0)<=1),
 'initial_physical_state_not_settled':F(1,125)>F(1,1000) and F(8,25)>F(1,50),
}
assert all(checks.values())
(P/'negative-check.json').write_text(json.dumps({'candidate_sha256':hashlib.sha256((P/'candidate.json').read_bytes()).hexdigest(),'checks':checks,'scope':'Exact failed certificate statements, not counterexamples to the fixed original theorem.'},indent=2)+'\n')
print(json.dumps(checks,indent=2))
