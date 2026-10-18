#!/usr/bin/env python3
"""Reviewer-written exact matrix checks; independent of builder verifier."""
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent
B=HERE.parent/'builder-04'
q=json.loads((B/'candidate.json').read_text());Q=[[F(v) for v in row] for row in q['Q']];assert q['alpha']==20
Z=lambda n,m:[[F(0) for _ in range(m)] for _ in range(n)]
def T(a):return list(map(list,zip(*a)))
def mul(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def add(a,b):return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def scale(c,a):return [[c*x for x in row] for row in a]
def eye(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def det(a):
    if not a:return F(1)
    return sum((-1)**j*a[0][j]*det([r[:j]+r[j+1:] for r in a[1:]]) for j in range(len(a)))
def inverse(a):
    n=len(a);b=[list(row)+e for row,e in zip(a,eye(n))]
    for i in range(n):
        k=next(j for j in range(i,n) if b[j][i]);b[i],b[k]=b[k],b[i]
        v=b[i][i];b[i]=[x/v for x in b[i]]
        for j in range(n):
            if j!=i:
                v=b[j][i];b[j]=[x-v*y for x,y in zip(b[j],b[i])]
    assert [row[:n] for row in b]==eye(n)
    return [row[n:] for row in b]
def minors(a,strict):
    out=[]
    for k in range(1,len(a)+1):
        for ix in combinations(range(len(a)),k):
            d=det([[a[i][j] for j in ix] for i in ix]);assert d>0 if strict else d>=0,(ix,d)
            out.append({'indices':ix,'determinant':str(d)})
    return out
def quadratic(a,x):return sum(x[i]*a[i][j]*x[j] for i in range(len(x)) for j in range(len(x)))
def A(r):return [[F(0),F(40),F(0)],[F(0),F(0),F(40)],[-r/2,-3*r/2,-3*r/2]]
def vecB(r):return [[F(0)],[F(0)],[r/2]]
def lmi(r):
    top=add(add(mul(A(r),Q),mul(Q,T(A(r)))),scale(F(20),Q));b=vecB(r)
    return [row+[b[i][0]] for i,row in enumerate(top)]+[[v[0] for v in b]+[F(-20)]]
P=inverse(Q)
assert mul(Q,P)==eye(3)==mul(P,Q)
reported=scale(F(1,68317631),[[F(x) for x in row] for row in [[49597375,60003000,25513875],[60003000,212058000,56866000],[25513875,56866000,102314375]]])
assert P==reported
D=[[F(80000),0,0],[0,F(2000),0],[0,0,F(50)]]
Di=inverse(D)
for r in [F(80),F(120),F(0),F(1)]:
    physical=[[F(0),F(1),F(0)],[F(0),F(0),F(1)],[-800*r,-60*r,-F(3,2)*r]]
    assert mul(mul(D,physical),Di)==A(r)
    assert mul(D,[[F(0)],[F(0)],[r/100]])==vecB(r)
C=[row+[F(0)] for row in P]+[[F(0),F(0),F(0),F(1)]]
def dissipation(r):return scale(F(-1),mul(mul(C,lmi(r)),C))
sos={80:[('1049162500/68317631',['1','172188/83933','1697537/419665','-408222/419665']),('16023486720000/5734103722723',['0','1','-1027193477/801174336','-759501739/801174336']),('175836125/25036698',['0','0','1','-576049/1406689']),('2503780/1406689',['0','0','0','1'])],120:[('2069717500/68317631',['1','1928201/827887','3128385/827887','-612333/827887']),('168148708317500/56559278575697',['0','1','-67304588102/67259483327','50814171525/67259483327']),('473255560000/67259483327',['0','0','1','-9877995/23662778']),('5957780/11831389',['0','0','0','1'])]}
def from_sos(terms,n):
    out=Z(n,n)
    for c,v in terms:
        c=F(c);assert c>0;v=[F(x) for x in v];out=add(out,[[c*x*y for y in v] for x in v])
    return out
report={'Q':[[str(v) for v in row] for row in Q],'P':[[str(v) for v in row] for row in P],'minors':{'Q':minors(Q,True)}}
for r in [80,120]:
    assert dissipation(F(r))==from_sos(sos[r],4)
    report['minors']['negative-LMI-'+str(r)]=minors(scale(F(-1),lmi(F(r))),True)
    # Independently expand the gradient derivative matrix, not the Q congruence.
    top=scale(F(-1),add(add(mul(T(A(F(r))),P),mul(P,A(F(r)))),scale(F(20),P)))
    pb=scale(F(-1),mul(P,vecB(F(r))))
    direct=[row+[pb[i][0]] for i,row in enumerate(top)]+[[x[0] for x in pb]+[F(20)]]
    assert direct==dissipation(F(r))
# Polynomial coefficients: at 0 and 1 equality proves the affine identity.
for r in [F(0),F(1)]:
    assert dissipation(r)==add(scale((120-r)/40,dissipation(F(80))),scale((r-80)/40,dissipation(F(120))))
coordinate_terms={1:[('102765761/273270524',['1','480024/396779','204111/396779']),('22801/396779',['0','1','518/151'])],2:[('160695495/273270524',['1','480024/396779','204111/396779']),('656100/396779',['0','1','151/810'])]}
for i in [1,2]:
    e=Z(3,3);e[i][i]=F(1);m=add(scale(Q[i][i],P),scale(F(-1),e))
    assert m==from_sos(coordinate_terms[i],3)
    report['minors']['coordinate-'+str(i)]=minors(m,False)
# Convex positive quadratic reaches its maximum over a box at a vertex.
box=[tuple(F(s)*b for s,b in zip(signs,[16,32,64])) for signs in product([-1,1],repeat=3)]
box_values=[quadratic(P,v) for v in box]
assert max(box_values)==F(995542624000,68317631)<1000000
# Original transformed cube is a parallelepiped inside that physical box.
original=[]
for signs in product([-1,1],repeat=3):
    z=[F(s,5000) for s in signs]
    scaled=(80000*z[0],80000*(z[1]-z[0]),80000*(z[2]-2*z[1]+z[0]))
    assert all(abs(q)<=b for q,b in zip(scaled,[16,32,64]))
    original.append({'z':[str(x) for x in z],'q':[str(x) for x in scaled],'V':str(quadratic(P,scaled))})
report['box_vertex_values']=[str(v) for v in box_values];report['original_cube_vertices']=original
entry=F(1)+F(999999,16**10)
assert entry<=F(101,100)
assert Q[1][1]*F(101,100)<4 and Q[2][2]*F(101,100)<1
report['entry_upper_bound']=str(entry)
report['scaled_speed_squared_upper']=str(Q[1][1]*F(101,100));report['scaled_acceleration_squared_upper']=str(Q[2][2]*F(101,100))
# Actual witness uses q=(16,-16,16)*exp(-40t); the switch changes both inputs.
y=[F(1,5000),F(-1,125),F(8,25)]
for r,wcoeff in [(F(80),F(0)),(F(120),F(4,75))]:
    assert y[1]==-40*y[0] and y[2]==-40*y[1]
    assert -40*y[2]==r*(-800*y[0]-60*y[1]-F(3,2)*y[2]+wcoeff)
assert abs(y[1])>F(1,1000) and abs(y[2])>F(1,50)
# Negative exact certificate controls.
assert quadratic(dissipation(F(80)),[F(2),F(0),F(0),F(2)]) + 20*(1-F(2)**2)<0
assert quadratic(dissipation(F(160)),[F(-2),F(2),F(-1),F(-1)])<0
assert quadratic(P,[F(16),F(0),F(0)])>1
report['passed']=True;report['strict_principal_minors']=sum(len(report['minors'][x]) for x in ['Q','negative-LMI-80','negative-LMI-120'])
(HERE/'exact-review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':True,'strict_principal_minors':report['strict_principal_minors'],'box_max':str(max(box_values)),'original_cube_max':str(max(F(x['V']) for x in original)),'entry_upper_bound':str(entry)}))
