"""Exact independent affine certificate. No import of root's policy code."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

BASE=Path(__file__).resolve().parent
root=json.loads((BASE/'inputs/result.json').read_text())
assert (BASE/'inputs/result.json').read_bytes()==(BASE/'root-replay/result.json').read_bytes()
# Affine forms are (constant, velocity coefficient, acceleration coefficient).
add=lambda x,y:tuple(a+b for a,b in zip(x,y))
scale=lambda c,x:tuple(c*a for a in x)
evaluate=lambda x,v,a:x[0]+x[1]*v+x[2]*a
one=lambda c:(c,F(0),F(0))
w=[F(51,50),F(101,100),F(1)]
target,R,D=F(9,200),F(2221,40000),F(1,2000)
A=F(127,100)+F(1,20)
V=F(1,50)+F(1,100)+A*D
J=F(12)*(F(121,100)+F(1,100)+A)
assert (A,V,J)==(F(33,25),F(1533,50000),F(762,25))
e=[F(1,1000)+V*D,F(1,100)+A*D,F(1,20)+J*D]
E=[e[0],e[0]+e[1]/4,e[0]+e[1]/2+e[2]/16]
assert list(map(str,e))==root['errors']
assert list(map(str,E))==root['coordinate_errors']
aforms=[one(F(0)),(F(0),F(1,4),F(0)),(F(0),F(1,2),F(1,16))]
kforms=[one(target)]
for i,j in product(range(3),repeat=2):
    numerator=add(add(aforms[i],scale(-1,aforms[j])),one(E[i]+E[j]))
    kforms.append(scale(1/(w[i]+w[j]),numerator))
uforms=[]
for i in range(3):
    assert w[0]-w[i]>=0
    for k in kforms:
        uforms.append(add(add(aforms[i],one(E[i])),scale(w[0]-w[i],k)))
corners=list(product([F(-561,50000),F(561,50000)],[F(-127,100),F(-1,5)]))
maxk=max(evaluate(k,v,a) for k in kforms for v,a in corners)
maxu=F(143,1000)+max(evaluate(u,v,a) for u in uforms for v,a in corners)
assert maxk==F(root['maximum_K']) and maxu==F(root['maximum_upper'])
assert w[0]*maxk<R and maxu<F(3,20)
records=[]
for v,a in corners:
    K=max(evaluate(k,v,a) for k in kforms)
    centers=[evaluate(f,v,a) for f in aforms]
    lo=max(centers[i]+E[i]-w[i]*K for i in range(3))
    hi=min(centers[i]-E[i]+w[i]*K for i in range(3))
    assert lo<=hi
    assert all(abs(centers[i]-lo)+E[i]<=w[i]*K for i in range(3))
    U=F(143,1000)+lo+w[0]*K
    assert U==F(143,1000)+max(evaluate(u,v,a) for u in uforms)
    records.append({'v':str(v),'a':str(a),'K':str(K),'upper':str(U)})

def at(v,a,mx):
    K=max(evaluate(k,v,a) for k in kforms)
    centers=[mx+evaluate(f,v,a) for f in aforms]
    c=max(centers[i]+E[i]-w[i]*K for i in range(3))
    return centers,K,c,c+w[0]*K
centers,K,c,U=at(F(-1,100),F(-117,100),F(7,50))
oldc=F(7,50)-F(1,100)/4-F(117,100)/32
oldK=max([target]+[(abs(x-oldc)+E[i])/w[i] for i,x in enumerate(centers)])
assert (K,c,U)==tuple(F(root['nominal'][k]) for k in ['K','c','upper'])
assert oldK==F(root['fair_nominal_old_center_variable_radius']['K'])
assert oldc+w[0]*oldK==F(root['fair_nominal_old_center_variable_radius']['upper'])
assert U<F(3,20)<oldc+w[0]*oldK
negative=at(F(1,50),F(-127,100),F(143,1000))
assert negative[-1]==F(15213033,100000000)>F(3,20)

# Derivative of k=-8(x-c)-6v-a/2 during pending q=-1.21.
# c is constant and cancels. The expression is multiaffine on this rectangle.
slopes=[-8*v-6*a-r*(F(-121,100)+d-a)/2
        for v,a,r,d in product([-V,V],[-A,A],[F(8),F(12)],[F(-1,100),F(1,100)])]
assert [min(slopes),max(slopes)]==list(map(F,root['pending_slope_range']))
assert 0<min(slopes) and max(slopes)<8
out={'passed':True,'root_replay_identical':True,'K_affine_forms':len(kforms),
     'U_affine_forms':len(uforms),'U_affine_corner_values_checked':len(uforms)*4,
     'continuous_certificate':'Every affine form at an interior point is a convex combination of its four corner values. Maxima preserve the common upper bound. mx contributes with coefficient one.',
     'K_forms':[[str(x) for x in k] for k in kforms],
     'U_forms':[[str(x) for x in u] for u in uforms],
     'corners':records,'max_K':str(maxk),'max_upper':str(maxu),
     'clearance_margin':str(F(3,20)-maxu),'cube_margin':str(R-w[0]*maxk),
     'pending_slope_range':[str(min(slopes)),str(max(slopes))],
     'slope_margin_to_8':str(8-max(slopes)),
     'nominal':{'K':str(K),'c':str(c),'upper':str(U),'command':str(-8*(F(7,50)-c)+F(6,100)+F(117,200))},
     'fair_old_center':{'K':str(oldK),'c':str(oldc),'upper':str(oldc+w[0]*oldK)},
     'wider_velocity_upper':str(negative[-1]),
     'scope':'Exact interval/affine and derivative arithmetic. No ODE theorem, trajectory safety, detector liveness or existence proof.'}
print(json.dumps(out,indent=2))
