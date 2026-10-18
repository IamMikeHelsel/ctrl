#!/usr/bin/env python3
"""Rationalize the one candidate and check strict rational LDL certificates."""
from pathlib import Path
from fractions import Fraction as F
import json
HERE=Path(__file__).resolve().parent
A=lambda r:[[F(x) for x in row]for row in [[0,1,0,0],[0,0,1,0],[0,0,-r,r],[-16,-12,-1,-2]]]
def trans(M):return [list(x)for x in zip(*M)]
def mul(A,B):return [[sum((a*b for a,b in zip(row,col)),F(0))for col in zip(*B)]for row in A]
def add(A,B):return [[a+b for a,b in zip(x,y)]for x,y in zip(A,B)]
def shift(A,c):return [[v-c*(i==j) for j,v in enumerate(row)]for i,row in enumerate(A)]
def ldl(A):
 n=len(A);L=[[F(i==j)for j in range(n)]for i in range(n)];D=[]
 for i in range(n):
  D.append(A[i][i]-sum((L[i][k]**2*D[k]for k in range(i)),F(0)))
  if D[-1]<=0:raise ValueError(('nonpositive pivot',i,str(D[-1])))
  for j in range(i+1,n):L[j][i]=(A[j][i]-sum((L[j][k]*L[i][k]*D[k]for k in range(i)),F(0)))/D[i]
 assert mul(mul(L,[[D[i]*(i==j)for j in range(n)]for i in range(n)]),trans(L))==A
 return L,D
src=json.loads((HERE/'candidate-float.json').read_text());attempts=[];success=None
for den in [10,100,1000]:
 P=[[F(round(v*den),den)for v in row]for row in src]
 Q={str(r):[[-v for v in row]for row in add(mul(trans(A(r)),P),mul(P,A(r)))]for r in [8,12]}
 mats={'P_minus_half_I':shift(P,F(1,2)),'Q8_minus_half_I':shift(Q['8'],F(1,2)),'Q12_minus_half_I':shift(Q['12'],F(1,2)),'upper_500I_minus_P':[[F(500)*(i==j)-P[i][j] for j in range(4)]for i in range(4)]}
 try:cert={k:ldl(M)for k,M in mats.items()}
 except ValueError as e:attempts.append({'denominator':den,'strict_margin':False,'reason':str(e)});continue
 attempts.append({'denominator':den,'strict_margin':True});success=(den,P,Q,mats,cert);break
assert success,'No exact strict candidate'
den,P,Q,mats,cert=success
encode=lambda M:[[str(x)for x in row]for row in M]
report={'passed':True,'rounding_attempts':attempts,'P':encode(P),'mu':'1/2','energy_lower':'1/2','energy_upper':'500','Q':{k:encode(M)for k,M in Q.items()},'LDL':{k:{'matrix':encode(mats[k]),'L':encode(v[0]),'D':[str(x)for x in v[1]],'positive_pivots':True,'identity_checked':True}for k,v in cert.items()},'interval_rule':'A(r)=(12-r)/4*A(8)+(r-8)/4*A(12); both coefficients nonnegative and sum to 1 for 8<=r<=12.','energy_decay':'V_prime<=-1/2*normSq(x)<=-V/1000; hence V(t)<=exp(-t/1000)*V(0).'}
(HERE/'exact-certificate.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'passed':True,'denominator':den,'P':report['P'],'pivots':{k:v['D']for k,v in report['LDL'].items()}},indent=2))
