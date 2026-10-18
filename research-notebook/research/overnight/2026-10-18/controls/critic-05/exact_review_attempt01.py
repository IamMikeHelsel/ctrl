#!/usr/bin/env python3
"""Independent exact polynomial review; no builder Python code is imported."""
from fractions import Fraction as F
from pathlib import Path
from math import comb, factorial
import json
HERE=Path(__file__).resolve().parent
B=HERE.parent/'builder-05'
width=F(1,5)
events=[(F(11,50),F(1,50)),(F(31,50),F(-1,50))]
knots=sorted({F(0),F(1,2),F(4)}|{time+m*width for time,_ in events for m in range(5)})
def polynomial(t):
    co=[F(0)]*5
    for tau,delta in events:
        for m in range(5):
            start=tau+m*width
            if t>=start:
                factor=delta*(-1)**m*comb(4,m)/(24*width**4)
                for k in range(5): co[k]+=factor*comb(4,k)*(-start)**(4-k)
    return co
def derivative(co): return [k*co[k] for k in range(1,len(co))]
def evaluate(co,t): return sum(c*t**k for k,c in enumerate(co))
def jets(t):
    co=polynomial(t); result=[]
    for _ in range(4): result.append(evaluate(co,t)); co=derivative(co)
    return result
checks=[]
for left,right in zip(knots,knots[1:]):
    p=polynomial((left+right)/2)
    for knot in (left,right):
        q=p
        for k in range(4):
            assert evaluate(q,knot)==jets(knot)[k],(left,right,knot,k)
            checks.append([str(left),str(right),str(knot),k,str(evaluate(q,knot))])
data=json.loads((B/'exact-witness-values.json').read_text())['rows']
rows=[]
for label, oldrows in data.items():
    bias=F(1,100) if label=='constant_bias' else F(1,200)
    for old in oldrows:
        t=F(old['t_s']);q,v,a,j=jets(t)
        rate=F(96) if label=='constant_bias' else F(92 if t<=F(1,2) else 100)
        w=bias if label=='constant_bias' else bias+j*(1/rate-F(1,96))
        x=q+bias/800
        u=a-800*(x-q)+j/96
        expected={'reference_x_m':q,'actual_x_m':x,'actual_v_m_per_s':v,
          'actual_a_m_per_s2':a,'actual_j_m_per_s3':j,'response_per_s':rate,
          'disturbance_m_per_s2':w,'command_m_per_s2':u}
        for k,val in expected.items(): assert F(old[k])==val,(label,t,k)
        assert j==rate*(u+w-a)
        assert abs(w)<=F(1,100)
        rows.append({'witness':label,'t':str(t),'exact_match':True,'ode':True})
assert jets(F(71,50))==[F(0)]*4
assert all(x==0 for x in polynomial(F(2)))
assert jets(F(1,2))[0]-2*F(1,5000)==F(679,250000)
oldrate=F(92);oldj=jets(F(1,2))[3]
oldw=F(1,200)+oldj*(1/oldrate-F(1,96))
tailx=F(1,160000);wrong=oldrate*(-800*tailx+oldw)
assert wrong==F(-1,48)
assert 100*(-800*tailx+F(1,200))==0
exact_factor=max(abs(1/F(r)-F(1,96)) for r in (92,100))
bounded_disturbance=F(1,200)+F(15,2)*exact_factor
assert bounded_disturbance==F(309,36800)<F(1,100)
result={'passed':True,'method':'Exact polynomial coefficients in global time, then formal polynomial derivatives. Finite arithmetic review, not a replacement for Lean all-time proofs.',
 'anchor_rows':rows,'cell_boundary_jet_equalities':checks,
 'worst_disturbance_from_claimed_jerk_bound':str(bounded_disturbance),
 'wrong_clock_rhs':str(wrong),'correct_clock_rhs':'0',
 'worst_progress_from_tracking_tube_m':'679/250000',
 'post_reference_tail_polynomial':[str(x) for x in polynomial(F(2))]}
(HERE/'exact-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':True,'anchors':len(rows),'cell_boundary_jet_equalities':len(checks),'wrong_clock_rhs':str(wrong)}))
