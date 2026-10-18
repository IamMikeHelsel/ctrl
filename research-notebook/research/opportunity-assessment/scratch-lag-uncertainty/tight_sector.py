"""Bounded feasibility spike. Numeric grids are NOT proofs.
Exact producer witnesses are UNVERIFIED until separately checked by Lean.
Main project and its frozen publication are read-only inputs.
"""
import json, sys, math, hashlib
from pathlib import Path
import numpy as np
import sympy as s
BASE=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent/"tight-sector"
OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(BASE/'lean-controls/scripts'))
from generate_interval_certificate import produce, ldl
P=s.Matrix([[s.Rational(38,5),s.Rational(257,25),5],
 [s.Rational(257,25),s.Rational(1319,50),s.Rational(769,50)],
 [5,s.Rational(769,50),s.Rational(278,25)]])
K=s.Matrix([[1,3,2]])
Pn=np.array(P,float);Kn=np.array(K,float)
h,r,a,L,q=s.symbols('h r a L q')
F=s.Matrix([[1,h,L*h*h],[0,1,h-L*r*h*h],[0,0,1-r*h+L*r*r*h*h]])
G=s.Matrix([(s.Rational(1,2)-L)*h*h,L*r*h*h,r*h-L*r*r*h*h])
A=F-G*a*K
# For exp(-r*h)=1-r*h+L*(r*h)^2, F and G are the exact
# zero-order-hold solution. For 0<=r*h<=1 existing exp_interpolation
# gives L in[0,1]. A is affine separately in a,L and quadratic in r.
report={'status':'exploration, not a complete uncertainty theorem',
 'model':"x'=v; v'=a; a'=r*(-a+clip_1(-x_n-3v_n-2a_n)+w_n)",
 'P':[[str(v) for v in row] for row in P.tolist()], 'numeric_grids':[]}
for eps in [.01,.05,.10,.20,.30]:
 worst=(1e9,None); response=(-1,None)
 for rr in np.linspace(1-eps,1+eps,25):
  for tt in np.linspace(.0001,.2,41):
   ee=math.exp(-rr*tt);d=-math.expm1(-rr*tt)
   FF=np.array([[1,tt,tt/rr-d/rr**2],[0,1,d/rr],[0,0,ee]])
   GG=np.array([[tt*tt/2-tt/rr+d/rr**2],[tt-d/rr],[d]])
   er=float((GG.T@Pn@GG)[0,0]/tt**2)
   if er>response[0]:response=(er,[rr,tt])
   for aa in [.4,1.]:
    AA=FF-GG*aa*Kn
    val=float(np.linalg.eigvalsh((Pn-AA.T@Pn@AA)/tt).min())
    if val<worst[0]:worst=(val,[rr,tt,aa])
 report['numeric_grids'].append({'rate_interval':[1-eps,1+eps],
  'samples':25*41*2,'min_divided_energy_margin':worst,
  'max_disturbance_energy_over_t_squared':response,'is_proof':False})
# Single selected exact attempt, with same controller, P, region and H.
lo=s.Rational(9,10); hi=s.Rational(11,10);margin=s.Rational(3,2)
report['selected']={'r_interval':[str(lo),str(hi)],'tau_interval':['10/11','10/9'],
 'H':'1/5','sector':['2/5','1'],'decay_margin':str(margin),'vertices':[]}
for ai,av in enumerate([s.Rational(2,5),s.Integer(1)]):
 for li,lv in enumerate([s.Integer(0),s.Integer(1)]):
  B=A.subs({a:av,L:lv,r:lo+(hi-lo)*q}).applyfunc(s.expand)
  power=[B.applyfunc(lambda z:s.Poly(z,q).nth(k)) for k in range(3)]
  coeff=[sum((power[k]*s.binomial(j,k)/s.binomial(2,k) for k in range(j+1)),s.zeros(3)) for j in range(3)]
  assert (sum((s.binomial(2,j)*q**j*(1-q)**(2-j)*coeff[j] for j in range(3)),s.zeros(3))-B).applyfunc(s.expand)==s.zeros(3)
  for j,V in enumerate(coeff):
   name=f'UncertainA{ai}L{li}R{j}'
   data={'P':report['P'],'A_coefficients':[[[str(s.Poly(V[i,k],h).nth(d)) for k in range(3)] for i in range(3)] for d in range(3)],'decay_margin':str(margin),'partition':['0','1/5']}
   rec={'name':name}
   try:
    source,witness=produce(data,name)
    (OUT/(name+'.lean')).write_text(source+f'\n#print axioms LeanControls.Generated.{name}.certified_decrease\n')
    (OUT/(name+'.input.json')).write_text(json.dumps(data,indent=2)+'\n')
    (OUT/(name+'.certificate.json')).write_text(json.dumps(witness,indent=2)+'\n')
    rec.update(status='exact rational witnesses produced; Lean not yet checked',
     min_ldl_pivot=str(min(s.Rational(d) for seg in witness['segments'] for C in seg['coefficients'] for d in C['d'])))
   except ValueError as e:rec.update(status='producer rejected',error=str(e))
   report['selected']['vertices'].append(rec)
# response / h is affine in h and L, degree2 in r: tensor Bernstein
# coefficient norms bound exact convex response once the bridge is checked.
C=s.Integer(16); resp=[]
for lv in [s.Integer(0),s.Integer(1)]:
 for tv in [s.Integer(0),s.Rational(1,5)]:
  R=(G/h).applyfunc(s.cancel).subs({L:lv,h:tv,r:lo+(hi-lo)*q}).applyfunc(s.expand)
  powr=[R.applyfunc(lambda z:s.Poly(z,q).nth(k)) for k in range(3)]
  for j in range(3):
   v=sum((powr[k]*s.binomial(j,k)/s.binomial(2,k) for k in range(j+1)),s.zeros(3,1))
   val=(v.T*P*v)[0]
   resp.append({'lambda':str(lv),'h':str(tv),'r_bernstein_index':j,'vector':[str(t) for t in v], 'energy':str(val),'below_C':bool(val<=C)})
report['response_vertices']={'C':str(C),'vertices':resp,'all_below_C':all(v['below_C'] for v in resp)}
eta=margin/(2*s.trace(P)); W=s.Rational(1,100); H=s.Rational(1,5);R0=s.Integer(12)
report['candidate_budget']={'eta':str(eta),'C':str(C),'W':str(W),
 'lhs':str((H+1/eta)*C*W**2),'rhs':str(eta*R0),
 'satisfied':bool((H+1/eta)*C*W**2<=eta*R0)}
(OUT/'feasibility.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
