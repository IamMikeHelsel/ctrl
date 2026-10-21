import warnings; warnings.filterwarnings('ignore')
import numpy as np, json
from core import *
from staticN import N_of, decomposition
rng = np.random.default_rng(0)
# n=7 KV control
A7 = np.array([[0,0,0,0,0,0,0],[0,0,0,0,0,0,0],[6,-5,-13,0,0,0,0],[-14,-18,0,0,0,0,0],[12,-12,11,0,0,0,0],[0,0,0,-6,0,-14,0],[0,0,0,6,-18,0,0]],float)
u,s,vt = np.linalg.svd(BK(A7)); K = skew_of(vt[0],7); Y = skew_of(u[:,0],7)
if np.sum(Y*L(A7,K))<0: Y=-Y
print("n=7 KV top pair: N(YK) =", N_of(Y@K), " expected >= k/s =", s[0]/np.linalg.norm(BS(A7),2))
# n=6 random unit skew pairs
vals=[]
for t in range(30):
    K = skew_of(rng.standard_normal(15)); K/=np.linalg.norm(K); Y = skew_of(rng.standard_normal(15)); Y/=np.linalg.norm(Y)
    P = Y@K
    vals.append((N_of(P), np.linalg.norm(P,'nuc'), np.linalg.norm((P+P.T)/2,'nuc')+np.linalg.norm((P-P.T)/2,'nuc')))
vals=np.array(vals); print("n=6 random: N in [%.4f, %.4f]; nuc in [%.4f,%.4f]; sym+skew nuc in [%.4f,%.4f]"%(vals[:,0].min(),vals[:,0].max(),vals[:,1].min(),vals[:,1].max(),vals[:,2].min(),vals[:,2].max()))
# K=Y, and n=6 SS-fail top pair, natural pairs
K = make_K(1,2,3); K/=np.linalg.norm(K); print("K=Y: N =", N_of(K@K))
from e07_dual_at import top_pair
for fn in ['logs/e05_n6_s1_e0.05_best.npy','logs/e05_n6_s2_e0.05_best.npy']:
    A = np.load(fn); K,Y,sk = top_pair(A); print(fn, "N(YK) =", N_of(Y@K), " 1/N =", 1/N_of(Y@K), " s/k =", np.linalg.norm(BS(A),2)/sk)
for t in range(5):
    A = rng.standard_normal((6,6)); K,Y,sk = top_pair(A); print("nat: N(YK) =", N_of(Y@K), " s/k =", np.linalg.norm(BS(A),2)/sk)
