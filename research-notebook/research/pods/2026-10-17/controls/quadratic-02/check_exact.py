#!/usr/bin/env python3
"""Independent arithmetic validation of recorded rational matrices and LDL factors."""
from pathlib import Path
from fractions import Fraction as F
import json,sys,hashlib
HERE=Path(__file__).resolve().parent
r=json.loads((HERE/'exact-certificate.json').read_text())
parse=lambda M:[[F(v)for v in row]for row in M]
T=lambda M:[list(v)for v in zip(*M)]
matmul=lambda A,B:[[sum((x*y for x,y in zip(row,col)),F(0))for col in zip(*B)]for row in A]
P=parse(r['P']);assert P==T(P)
mu=F(r['mu']);lo=F(r['energy_lower']);hi=F(r['energy_upper']);assert mu>0 and lo>0 and hi>0
A=lambda rate:[[F(v)for v in row]for row in [[0,1,0,0],[0,0,1,0],[0,0,-rate,rate],[-16,-12,-1,-2]]]
expected={'P_minus_half_I':[[P[i][j]-lo*(i==j)for j in range(4)]for i in range(4)],'upper_500I_minus_P':[[hi*(i==j)-P[i][j]for j in range(4)]for i in range(4)]}
for rate in [8,12]:
 AP=matmul(T(A(rate)),P);PA=matmul(P,A(rate))
 Q=[[-AP[i][j]-PA[i][j]for j in range(4)]for i in range(4)]
 assert Q==parse(r['Q'][str(rate)])
 expected[f'Q{rate}_minus_half_I']=[[Q[i][j]-mu*(i==j)for j in range(4)]for i in range(4)]
for k,M in expected.items():
 c=r['LDL'][k];L=parse(c['L']);D=[F(x)for x in c['D']]
 assert all(d>0 for d in D)
 assert all(L[i][i]==1 for i in range(4))
 assert all(L[i][j]==0 for i in range(4)for j in range(i+1,4))
 LD=[[L[i][j]*D[j]for j in range(4)]for i in range(4)]
 assert matmul(LD,T(L))==M==parse(c['matrix'])
# Exact checks of the affine identity at the coefficient level.
for i in range(4):
 for j in range(4):
  assert A(0)[i][j]==3*A(8)[i][j]-2*A(12)[i][j]
  assert A(1)[i][j]-A(0)[i][j]==(A(12)[i][j]-A(8)[i][j])/4
assert mu/hi==F(1,1000)
# The false strengthened mu=100 fails on the first basis vector at r=8.
assert F(r['Q']['8'][0][0])<100
out={'passed':True,'matrices_checked':list(expected),'arithmetic':'Python Fraction integers and rational arithmetic only','python':sys.version,'certificate_sha256':hashlib.sha256((HERE/'exact-certificate.json').read_bytes()).hexdigest(),'mu':str(mu),'energy_lower':str(lo),'energy_upper':str(hi),'decay_rate':str(mu/hi),'false_mu_100_counterexample':'x=(1,0,0,0), Q8 quadratic value=1144/25<100'}
(HERE/'exact-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
