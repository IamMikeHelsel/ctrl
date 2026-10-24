"""Exact check of the 7x7 integer matrix recorded in the ctrl pod as the arXiv:2608.20875 counterexample:
claimed  ||L_A|Sym||^2 < 1196 < ||L_A|Skew||^2."""
import numpy as np
from fractions import Fraction as Fr
from exact import mat, ratio_lower, s2_upper
from core import bases, op_mats, top_pair, s_k
A7=[[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[6,-5,-13,0,0,0,0],[-14,-18,0,0,0,0,0],[12,-12,11,0,0,0,0],[0,0,0,-6,0,-14,0],[0,0,0,6,-18,0,0]]
Af=np.array(A7,float); s,k=s_k(Af); print('float s^2',s**2,'k^2',k**2,'k/s',k/s)
S,Kb=bases(7); LS,LK=op_mats(Af); kk,Y,K,sv=top_pair(LK,Kb)
K=K/np.abs(K).max()
Kt=[[Fr(0)]*7 for _ in range(7)]
for i in range(7):
    for j in range(i+1,7):
        q=Fr(round(K[i,j]*10**6),10**6); Kt[i][j]=q; Kt[j][i]=-q
A=mat(A7); lb=ratio_lower(A,Kt)
print('[exact] k^2 >= ',float(lb),' > 1196:',lb>1196)
print('[exact] s^2 < 1196:',s2_upper(A,Fr(1196)))
