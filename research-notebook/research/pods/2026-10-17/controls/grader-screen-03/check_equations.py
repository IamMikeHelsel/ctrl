#!/usr/bin/env python3
"""Independent exact coefficient/scaling and equilibrium checks for the fixed model."""
from pathlib import Path
from fractions import Fraction as F
import json
HERE=Path(__file__).resolve().parent
sigma=F(10);lam=F(20);scale=[F(1),sigma,sigma**2,sigma**2]
checks=[]
for rho in [F(8),F(10),F(12)]:
 r=rho*sigma
 Ap=[[0,1,0,0],[0,0,1,0],[0,0,-r,r],[-8*lam*sigma**2,-6*lam*sigma,-lam/2,-lam]]
 An=[[F(Ap[i][j])*scale[j]/scale[i]/sigma for j in range(4)]for i in range(4)]
 assert An==[[0,1,0,0],[0,0,1,0],[0,0,-rho,rho],[-16,-12,-1,-2]]
 for k in [F(5,48),F(29,48)]:
  for w in [F(0),F(1,100),F(-1,100)]:
   for j in [F(10),F(-10),F(0)]:
    gp=[F(0),F(0),r*w-j,(lam*k/sigma-1)*j]
    gn=[gp[i]/scale[i]/sigma for i in range(4)]
    wn=w/sigma**2;jn=j/sigma**3
    assert gn==[0,0,rho*wn-jn,(2*k-1)*jn]
    xi=[(wn+(k-1/rho-F(1,2))*jn)/8,F(0),F(0),jn/rho-wn]
    assert all(sum(An[i][a]*xi[a]for a in range(4))+gn[i]==0 for i in range(4))
    eta=[scale[i]*xi[i]for i in range(4)]
    assert r*(eta[3]+w-eta[2])==j
    target_minus_u=-8*sigma**2*eta[0]-6*sigma*eta[1]-eta[2]/2-eta[3]+k*j/sigma
    assert lam*target_minus_u==j
    checks.append({'rho':str(rho),'kappa':str(k),'w_physical':str(w),'j_physical':str(j),'position_error_equilibrium_m':str(xi[0]),'b_physical_equilibrium':str(eta[3]),'actual_jerk_equilibrium':str(j),'filter_u_prime_equilibrium':str(j),'residuals_exact_zero':True})
report={'passed':True,'arithmetic':'Fraction exact rational coefficient equality','normalized_time':'tau=10*t','normalized_state':'xi=(ex,ev/10,ea/100,(u-q2)/100)','normalized_rate':'rho=r_physical/10','normalized_disturbance':'wn=w_physical/100','normalized_jerk':'jn=j_physical/1000','physical_filter_rate':'20/s','homogeneous_matrix':'[[0,1,0,0],[0,0,1,0],[0,0,-rho,rho],[-16,-12,-1,-2]]','forcing':'(0,0,rho*wn-jn,(2*kappa-1)*jn)','equilibrium_tests':checks}
(HERE/'equations-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':True,'exact_equilibrium_cases':len(checks)}))
