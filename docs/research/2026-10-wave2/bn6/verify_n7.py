import os
import json, time
from fractions import Fraction as Fr
from exact import *
d=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'cert_n7.json')))
A=mat(d['A']); K=mat(d['K'])
assert all(K[i][j]==-K[j][i] for i in range(7) for j in range(7))
t=time.time()
k2=ratio_lower(A,K)
print('k^2 >=',float(k2))
# find the smallest c of form k2/(1+eps) for which PD holds
for eps in [Fr(1,10),Fr(1,100),Fr(14,1000),Fr(145,10000),Fr(146,10000)]:
    c=k2/((1+eps))
    print('eps',float(eps),'s^2 < k2/(1+eps):',s2_upper(A,c))
print('time',time.time()-t)
