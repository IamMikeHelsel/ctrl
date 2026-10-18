from pathlib import Path
import json, platform, sys, time, hashlib
import cvxpy as cp
import numpy as np
from fractions import Fraction as F
P=Path(__file__).resolve().parent
alphas=[4,8,12,16,20,24,32,40]
def out(v):
 if isinstance(v,np.ndarray): return v.tolist()
 if isinstance(v,np.generic): return v.item()
 raise TypeError(type(v).__name__)
def matrix(r):return np.array([[0.,40.,0.],[0.,0.,40.],[-r/2,-3*r/2,-3*r/2]])
def ldl(X):
 n=len(X); L=[[F(i==j) for j in range(n)] for i in range(n)]; d=[]
 for j in range(n):
  dj=X[j][j]-sum(L[j][k]**2*d[k] for k in range(j)); d.append(dj)
  if dj<=0:return False, list(map(str,d))
  for i in range(j+1,n): L[i][j]=(X[i][j]-sum(L[i][k]*L[j][k]*d[k] for k in range(j)))/dj
 return True,list(map(str,d))
def matinv(X):
 n=len(X); Y=[list(X[i])+[F(i==j) for j in range(n)] for i in range(n)]
 for j in range(n):
  if not Y[j][j]:
   k=next(k for k in range(j+1,n) if Y[k][j]);Y[j],Y[k]=Y[k],Y[j]
  p=Y[j][j];Y[j]=[x/p for x in Y[j]]
  for k in range(n):
   if k!=j:
    v=Y[k][j];Y[k]=[a-v*b for a,b in zip(Y[k],Y[j])]
 return [row[n:] for row in Y]
def block(Q,a,r):
 A=[[0,40,0],[0,0,40],[-F(r,2),-F(3*r,2),-F(3*r,2)]];B=[0,0,F(r,2)]
 X=[[F(0) for _ in range(4)] for _ in range(4)]
 for i in range(3):
  for j in range(3):X[i][j]=sum(A[i][k]*Q[k][j]+Q[i][k]*A[j][k] for k in range(3))+a*Q[i][j]
  X[i][3]=X[3][i]=B[i]
 X[3][3]=-F(a)
 return X
def exact(Q,a):
 oq,pq=ldl(Q); result={'Q_PD':oq,'Q_LDL_pivots':pq,'endpoint':{}}
 good=oq
 for r in (80,120):
  X=block(Q,a,r);om,pm=ldl([[-x for x in row] for row in X]);result['endpoint'][str(r)]={'minus_M_PD':om,'pivots':pm};good &= om
 bounds=Q[1][1]<=F(9,4) and Q[2][2]<=F(81,100);good &= bounds;result['diagonal_bounds']=bounds
 if oq:
  Pinv=matinv(Q);b=[16,32,64];M0=sum(abs(Pinv[i][j])*b[i]*b[j] for i in range(3) for j in range(3));C2=1+(max(F(1),M0)-1)/F(2048)**(a//4)
  bv=Q[1][1]*C2<=4;ba=Q[2][2]*C2<=1;good &= bv and ba
  result.update(P=[[str(x) for x in row] for row in Pinv],M0=str(M0),C2=str(C2),entry_velocity=bv,entry_acceleration=ba,Q11_C2=str(Q[1][1]*C2),Q22_C2=str(Q[2][2]*C2))
 result['pass']=bool(good);return result
results=[];selected=None
meta={'python':sys.version,'platform':platform.platform(),'cvxpy':cp.__version__,'numpy':np.__version__,'solvers':cp.installed_solvers()}
(P/'environment.json').write_text(json.dumps(meta,indent=2)+'\n')
for a in alphas:
 Q=cp.Variable((3,3),symmetric=True);s=cp.Variable(); cons=[Q-s*np.eye(3)>>0,Q[1,1]<=2.25,Q[2,2]<=.81,s<=1]
 for r in (80,120):
  A=matrix(r);B=np.array([[0.],[0.],[r/2]])
  M=cp.bmat([[A@Q+Q@A.T+a*Q,B],[B.T,np.array([[-a]])]])
  cons.append(-M-s*np.eye(4)>>0)
 problem=cp.Problem(cp.Maximize(s),cons); item={'alpha':a,'started':time.time()}; start=time.monotonic()
 try:
  solver='CLARABEL' if 'CLARABEL' in cp.installed_solvers() else 'SCS'; item['solver']=solver
  opts={'max_iter':300,'tol_gap_abs':1e-10,'tol_feas':1e-10,'tol_gap_rel':1e-10} if solver=='CLARABEL' else {'max_iters':50000,'eps':1e-8}
  problem.solve(solver=solver,verbose=False,**opts);item.update(status=problem.status,margin=s.value,Q=Q.value)
  if Q.value is not None:
   item['eigenvalues_Q']=np.linalg.eigvalsh(Q.value); item['endpoint_max_eigenvalues']={str(r):float(np.linalg.eigvalsh(np.block([[matrix(r)@Q.value+Q.value@matrix(r).T+a*Q.value,np.array([[0.],[0.],[r/2]])],[np.array([[0.,0.,r/2]]),np.array([[-a]])]])).max()) for r in (80,120)}
   item['rationalization']=[]
   for den in [1000,10000,100000,1000000,100000000]:
    q=[[F(int(round(float(Q.value[i,j])*den)),den) for j in range(3)] for i in range(3)];check=exact(q,a);entry={'denominator':den,'Q':[[str(x) for x in row] for row in q],'check':check};item['rationalization'].append(entry)
    if check['pass'] and selected is None:
     selected={'alpha':a,'Q':entry['Q'],'rounding_denominator':den,'selected_by':'first exact pass in fixed alpha/denominator order'}
     (P/'candidate.json').write_text(json.dumps(selected,indent=2)+'\n'); print('CANDIDATE',a,den,flush=True)
 except Exception as exc:item.update(error=repr(exc))
 item['seconds']=time.monotonic()-start;results.append(item);(P/'search-results.json').write_text(json.dumps(results,indent=2,default=out)+'\n');print('RESULT',a,item.get('status'),item.get('margin'),item.get('error'),flush=True)
print('SELECTED',selected,flush=True)
