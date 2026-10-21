import numpy as np
from scipy.linalg import expm
K=np.array([8,6,.5]); r=8; T=.001; D=.0005
P=np.array([[0,1,0],[0,0,1],[0,0,-r]],float); b=np.array([0,0,r])
def trans(t):
 E=expm(np.block([[P,b[:,None]],[np.zeros((1,4))]])*t)
 return E[:3,:3],E[:3,3]
AD,BD=trans(D); AF,BF=trans(T-D); AT,BT=trans(T)
J=AF@BD
F=np.block([[AT-BF[:,None]*K,J[:,None]],[-K[None,:],np.zeros((1,1))]])
B=np.r_[8*BF,8.]; G=np.column_stack([np.r_[BF,1],np.r_[J,0],np.r_[BF,0]])
S=np.array([[1,0,0,0],[1,.25,0,0],[1,.5,.0625,0],[8,6,.5,1.]])
# residual coordinate last scaled to metres
S[3]/=24
Fi=S@F@np.linalg.inv(S); Gi=S@G
print('eigen',np.linalg.eigvals(F)); print('Fcoord',Fi)
for m in [100,500,1000,2000,5000]:
 A=np.eye(4); V=np.zeros((4,3)); M=np.zeros(4)
 for i in range(m):
  M+=np.abs(A@Gi)@np.array([.093,.01,.01]); A=A@Fi
 rho=np.linalg.norm(A,np.inf)
 print(m,rho,M,'tail ball',max(M)/(1-rho) if rho<1 else None)
A=np.eye(4); noise=np.zeros(4); worst=np.zeros(4); B=.014
for i in range(2001):
 worst=np.maximum(worst,np.sum(np.abs(A),axis=1)*B+noise)
 noise+=np.abs(A@Gi)@np.array([.093,.01,.01]); A=A@Fi
print('phase bound',worst,'terminal m-step',np.sum(np.abs(np.linalg.matrix_power(Fi,2000)),axis=1)*B+noise)
