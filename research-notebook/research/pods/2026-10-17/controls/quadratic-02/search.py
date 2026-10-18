#!/usr/bin/env python3
"""One bounded common-quadratic feasibility search at lambda=2, r endpoints 8,12."""
from pathlib import Path
from fractions import Fraction as F
import json,time,numpy as np
from scipy.linalg import solve_continuous_lyapunov
from scipy.optimize import linprog
HERE=Path(__file__).resolve().parent
A=lambda r:np.array([[0,1,0,0],[0,0,1,0],[0,0,-r,r],[-16,-12,-1,-2]],dtype=float)
inds=[(i,j) for i in range(4) for j in range(i,4)]
basis=[]
for i,j in inds:
 B=np.zeros((4,4));B[i,j]=B[j,i]=1;basis.append(B)
basis=np.array(basis)
forms=[basis]+[np.array([-A(r).T@B-B@A(r) for B in basis])for r in [8,12]]
c=np.array([1. if i==j else 0. for i,j in inds])
rows=[]
for form in forms:
 for v in np.eye(4):rows.append(np.array([v@B@v for B in form]))
start=time.monotonic();history=[];candidate=None
for k in range(160):
 if time.monotonic()-start>120:break
 res=linprog(c,A_ub=-np.array(rows),b_ub=-np.ones(len(rows)),bounds=[(None,None)]*10,method='highs')
 if not res.success:
  history.append({'iteration':k,'status':res.status,'message':res.message});break
 vals=[]
 for form in forms:
  M=np.einsum('i,ijk->jk',res.x,form)
  ev,vec=np.linalg.eigh(M);vals.append(ev.tolist())
  for index in np.flatnonzero(ev<1-1e-7):
   v=vec[:,index];rows.append(np.array([v@B@v for B in form]))
 history.append({'iteration':k,'trace':float(res.fun),'eigenvalues':vals,'constraints':len(rows)})
 if all(e[0]>=1-1e-7 for e in vals):candidate=np.einsum('i,ijk->jk',res.x,basis);break
mid=solve_continuous_lyapunov(A(10).T,-np.eye(4))
report={'fixed_parameters':{'sigma':1,'lambda':2,'rate_endpoints':[8,12]},'method':'HiGHS linear cuts from violated eigenvectors; maximum 160 LP solves or 120 seconds; no parameter sweep','midpoint_candidate_endpoint_eigenvalues':{str(r):np.linalg.eigvalsh(-A(r).T@mid-mid@A(r)).tolist()for r in [8,12]},'history':history,'seconds':time.monotonic()-start,'candidate_found':candidate is not None}
if candidate is not None:
 report['floating_candidate']=candidate.tolist()
 (HERE/'candidate-float.json').write_text(json.dumps(candidate.tolist(),indent=2)+'\n')
(HERE/'search-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'candidate_found':report['candidate_found'],'seconds':report['seconds'],'last':history[-1]},indent=2))
if candidate is not None:print(candidate)
