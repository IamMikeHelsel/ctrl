"""Separate exact certificate verifier: all principal minors, no SDP imports."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib,itertools
P=Path(__file__).resolve().parent
candidate=P/'candidate.json';raw=candidate.read_bytes();data=json.loads(raw)
Q=[[F(x) for x in row] for row in data['Q']];alpha=F(data['alpha'])
def det(A):
 if len(A)==0:return F(1)
 return sum((-1)**j*A[0][j]*det([row[:j]+row[j+1:] for row in A[1:]]) for j in range(len(A)))
def principal(A):
 return {','.join(map(str,I)):str(det([[A[i][j] for j in I] for i in I])) for k in range(1,len(A)+1) for I in itertools.combinations(range(len(A)),k)}
def transpose(A):return list(map(list,zip(*A)))
def mm(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def inverse(A):
 n=len(A);d=det(A);return [[(-1)**(i+j)*det([[A[k][l] for l in range(n) if l!=i] for k in range(n) if k!=j])/d for j in range(n)] for i in range(n)]
assert Q==transpose(Q);Pmat=inverse(Q);assert mm(Q,Pmat)==[[F(i==j) for j in range(3)] for i in range(3)]
report={'candidate_sha256':hashlib.sha256(raw).hexdigest(),'method':'Fraction exact arithmetic and ALL nonempty principal minors; inverse via cofactors','alpha':str(alpha),'Q_minors':principal(Q),'endpoints':{}}
assert all(F(v)>0 for v in report['Q_minors'].values())
for r in (80,120):
 A=[[0,40,0],[0,0,40],[-F(r,2),-F(3*r,2),-F(3*r,2)]];AQ=mm(A,Q);QAt=mm(Q,transpose(A));B=[0,0,F(r,2)]
 minusM=[[-AQ[i][j]-QAt[i][j]-alpha*Q[i][j] for j in range(3)]+[-B[i]] for i in range(3)]+[[-b for b in B]+[alpha]]
 minors=principal(minusM);assert all(F(v)>0 for v in minors.values());report['endpoints'][str(r)]={'minusM':[[str(x) for x in row] for row in minusM],'all_principal_minors':minors}
b=[16,32,64];M0=sum(abs(Pmat[i][j])*b[i]*b[j] for i in range(3) for j in range(3));C2=1+(max(F(1),M0)-1)/F(2048)**(int(alpha)//4)
assert Q[1][1]<=F(9,4) and Q[2][2]<=F(81,100)
assert Q[1][1]*C2<=4 and Q[2][2]*C2<=1
# A deliberately looser entry bound for a simpler Lean bridge: V(0)<=10^6,
# exp(-40)<=16^(-10), derived from existing exp(-4)<=1/16.
Cloose=1+F(999999,16**10)
assert M0<=10**6 and Q[1][1]*Cloose<=4 and Q[2][2]*Cloose<=1
report.update(P=[[str(x) for x in row] for row in Pmat],M0=str(M0),M0_decimal=float(M0),C2=str(C2),Q11_C2=str(Q[1][1]*C2),Q22_C2=str(Q[2][2]*C2),loose_M0=10**6,loose_C2=str(Cloose),pass_exact_arithmetic=True)
(P/'exact-check.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
