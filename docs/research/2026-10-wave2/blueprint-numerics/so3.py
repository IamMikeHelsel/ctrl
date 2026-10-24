import numpy as np
rng=np.random.default_rng(0)
def hat(v): return np.array([[0,-v[2],v[1]],[v[2],0,-v[0]],[-v[1],v[0],0]])
def vee(S): return np.array([S[2,1],S[0,2],S[1,0]])
def randrot():
    q,r=np.linalg.qr(rng.normal(size=(3,3))); q=q@np.diag(np.sign(np.diag(r)))
    if np.linalg.det(q)<0: q[:,0]*=-1
    return q
def expm(S):
    from math import factorial
    out=np.eye(3); term=np.eye(3)
    for k in range(1,40): term=term@S/k; out=out+term
    return out
mx=[0]*10
for _ in range(2000):
    R=randrot(); Rd=randrot(); E=Rd.T@R
    psi=0.5*np.trace(np.eye(3)-E); eR=0.5*vee(E-E.T)
    mx[0]=max(mx[0],abs(eR@eR-psi*(2-psi)))                     # ||eR||^2 = psi(2-psi)
    mx[1]=max(mx[1],np.linalg.norm(E@eR-eR))                     # E eR = eR
    mx[2]=max(mx[2],abs(np.trace(E@E)-(np.trace(E)**2-2*np.trace(E))))  # tr E^2 = t^2-2t
    adj=np.linalg.det(E)*np.linalg.inv(E); mx[3]=max(mx[3],np.linalg.norm(adj-E.T))
    a,b=rng.normal(size=3),rng.normal(size=3)
    mx[4]=max(mx[4],np.linalg.norm(np.cross(E@a,E@b)-E@np.cross(a,b)))
    # derivative check: Rdot = R hat(W), Rddot = Rd hat(Wd)
    W,Wd=rng.normal(size=3),rng.normal(size=3); h=1e-6
    Psi=lambda R,Rd: 0.5*np.trace(np.eye(3)-Rd.T@R)
    num=(Psi(R@expm(h*hat(W)),Rd@expm(h*hat(Wd)))-Psi(R@expm(-h*hat(W)),Rd@expm(-h*hat(Wd))))/(2*h)
    eW=W-E.T@Wd
    mx[5]=max(mx[5],abs(num-eR@eW))
    # eR dot = C(E) eW, C(E)=0.5(tr(E^T) I - E^T)
    eRf=lambda R,Rd: 0.5*vee(Rd.T@R-R.T@Rd)
    numv=(eRf(R@expm(h*hat(W)),Rd@expm(h*hat(Wd)))-eRf(R@expm(-h*hat(W)),Rd@expm(-h*hat(Wd))))/(2*h)
    CE=0.5*(np.trace(E.T)*np.eye(3)-E.T)
    mx[6]=max(mx[6],np.linalg.norm(numv-CE@eW))
    mx[7]=max(mx[7],np.linalg.norm(CE,2))                         # ||C(E)|| <= 1
    # spectral-free bound: |x . C(E) y| <= ... check  ||C(E) y||^2 <= ||y||^2 via CE^T CE <= I
    mx[8]=max(mx[8],np.max(np.linalg.eigvalsh(CE.T@CE-np.eye(3))))
print("max |eR^2-psi(2-psi)|",mx[0]); print("max |E eR - eR|",mx[1]); print("tr E^2 identity",mx[2]); print("adj E = E^T",mx[3])
print("cross equivariance",mx[4]); print("dPsi/dt = eR.eW (fd err)",mx[5]); print("deR/dt=C eW (fd err)",mx[6]); print("max ||C(E)||_2",mx[7]); print("max eig(C^TC - I)",mx[8])
# closed form of C^T C ?
E=randrot(); CE=0.5*(np.trace(E)*np.eye(3)-E.T); t=np.trace(E)
print("C^T C =? ((1+t)/2)^2... eigen", np.linalg.eigvalsh(CE.T@CE), ((t+1)/2)**2/1, (t+1)/4*0+ ( (3-t)/2*(2-(3-t)/2) )/4 )
print("---- extra identities")
m=[0]*4
for _ in range(2000):
    E=randrot(); t=np.trace(E); I=np.eye(3)
    S=E+E.T-(t-1)*I; m[0]=max(m[0],np.linalg.norm(S@S-(3-t)*S)); m[1]=min(m[1],np.min(np.linalg.eigvalsh(S)))
    X=rng.normal(size=(3,3)); adj=np.linalg.det(X)*np.linalg.inv(X); tx=np.trace(X)
    m[2]=max(m[2],np.linalg.norm(adj-(X@X-tx*X+np.trace(adj)*I)))   # 3x3 adjugate = CH quotient (all X)
    m[3]=max(m[3],abs(np.trace(adj)-0.5*(tx**2-np.trace(X@X))))
print("S^2=(3-t)S",m[0],"min eig S",m[1],"adj X = X^2 - tX + s I",m[2],"tr adj = e2",m[3])
